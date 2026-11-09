'use strict';
// Vault Sync: keeps this vault in sync with the Vault Sync server on the VPS (over Tailscale), so the
// Mac, the PC and both iPhones share one vault. The server commits every change to git and pushes
// to GitHub. Plain JS, no build step. The sync logic (SyncEngine) only talks to two small interfaces,
// a file system and a server, so it can be tested outside Obsidian.

let obsidian = {};
try { obsidian = require('obsidian'); } catch (e) { /* running under the Node test harness */ }
const { Plugin, PluginSettingTab, Setting, Notice, Modal, Platform, requestUrl, debounce, TFile, TFolder } = obsidian;

const DEFAULT_SERVER = 'https://life-agent.tailb2c60d.ts.net';
const MASS_DELETE = 25;          // ask before a sync deletes more files than this
const PARALLEL = 4;              // transfers at once
const INTERVAL_MIN = 3;          // background sync every N minutes while open
const EDIT_DELAY_MS = 8000;      // sync this long after the last edit
// Never synced: git internals and files that belong to one device. Same list as the server.
const ALWAYS_IGNORE = [
  '.git/', '.trash/', '**/.DS_Store', '**/__pycache__/', '**/Thumbs.db', '**/desktop.ini',
  '.obsidian/workspace.json', '.obsidian/workspace-mobile.json', '.obsidian/workspaces.json',
  '.obsidian/plugins/vault-sync/data.json',
];

// ---------- helpers ----------

function globToRe(glob) {
  let re = '';
  for (let i = 0; i < glob.length; i++) {
    const c = glob[i];
    if (c === '*') re += '[^/]*';
    else if (c === '?') re += '[^/]';
    else if (c === '[') { const j = glob.indexOf(']', i); if (j > i) { re += glob.slice(i, j + 1); i = j; } else re += '\\['; }
    else re += c.replace(/[.+^${}()|\\]/g, '\\$&');
  }
  return new RegExp('^' + re + '$');
}

function compileIgnore(lines) {
  return lines.map((raw) => {
    let pat = raw.trim();
    let anchored = pat.startsWith('/');
    pat = pat.replace(/^\/+/, '');
    const isDir = pat.endsWith('/');
    pat = pat.replace(/\/+$/, '');
    if (pat.startsWith('**/')) { pat = pat.slice(3); anchored = false; }
    return { re: globToRe(pat), isDir, full: anchored || pat.includes('/') };
  });
}

function isIgnored(path, rules) {
  const parts = path.split('/');
  for (const r of rules) {
    const n = parts.length + (r.isDir ? 0 : 1);
    for (let i = 1; i < n; i++) {
      const cand = parts.slice(0, i).join('/');
      if (r.full ? r.re.test(cand) : r.re.test(parts[i - 1])) return true;
    }
  }
  return false;
}

function parseIgnoreFile(text) {
  return text.split(/\r?\n/).map((l) => l.trim()).filter((l) => l && !l.startsWith('#'));
}

// git blob hash: sha1("blob <len>\0" + bytes). Web Crypto when available, else a small JS SHA-1.
async function gitHash(buf) {
  const data = new Uint8Array(buf);
  const head = new TextEncoder().encode(`blob ${data.length}\0`);
  const all = new Uint8Array(head.length + data.length);
  all.set(head, 0); all.set(data, head.length);
  const subtle = (globalThis.crypto && globalThis.crypto.subtle) || null;
  if (subtle) {
    const d = await subtle.digest('SHA-1', all);
    return [...new Uint8Array(d)].map((b) => b.toString(16).padStart(2, '0')).join('');
  }
  return sha1js(all);
}

function sha1js(bytes) {
  const l = bytes.length, words = new Uint32Array(((l + 8) >> 6 << 4) + 16);
  for (let i = 0; i < l; i++) words[i >> 2] |= bytes[i] << (24 - (i % 4) * 8);
  words[l >> 2] |= 0x80 << (24 - (l % 4) * 8);
  words[words.length - 1] = l * 8;
  let [a, b, c, d, e] = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0];
  const w = new Uint32Array(80);
  for (let i = 0; i < words.length; i += 16) {
    for (let t = 0; t < 80; t++) w[t] = t < 16 ? words[i + t] : ((x) => (x << 1) | (x >>> 31))(w[t - 3] ^ w[t - 8] ^ w[t - 14] ^ w[t - 16]);
    let [A, B, C, D, E] = [a, b, c, d, e];
    for (let t = 0; t < 80; t++) {
      const f = t < 20 ? (B & C) | (~B & D) : t < 40 ? B ^ C ^ D : t < 60 ? (B & C) | (B & D) | (C & D) : B ^ C ^ D;
      const k = t < 20 ? 0x5a827999 : t < 40 ? 0x6ed9eba1 : t < 60 ? 0x8f1bbcdc : 0xca62c1d6;
      const tmp = (((A << 5) | (A >>> 27)) + f + E + k + w[t]) >>> 0;
      E = D; D = C; C = (B << 30) | (B >>> 2); B = A; A = tmp;
    }
    a = (a + A) >>> 0; b = (b + B) >>> 0; c = (c + C) >>> 0; d = (d + D) >>> 0; e = (e + E) >>> 0;
  }
  return [a, b, c, d, e].map((x) => (x >>> 0).toString(16).padStart(8, '0')).join('');
}

async function pool(items, n, fn) {
  let i = 0;
  const workers = Array.from({ length: Math.min(n, items.length) }, async () => {
    while (i < items.length) { const item = items[i++]; await fn(item); }
  });
  await Promise.all(workers);
}

// ---------- sync engine ----------
// fs:  list() -> [{path, size, mtime}], read(path) -> ArrayBuffer, write(path, buf) -> {size, mtime},
//      remove(path), exists(path)
// api: changes(since) -> {seq, changes:[{path, hash, deleted, seq}]}, get(path) -> {data, hash},
//      put(path, data, base, hash) -> {status, hash, copy}, del(path, base) -> {status}
// state: {seq, initialized, files: {path: {hash, size, mtime}}}

class SyncEngine {
  constructor({ fs, api, state, save, confirm, log }) {
    Object.assign(this, { fs, api, state, save, confirm, log: log || (() => {}) });
    this.state.files = this.state.files || {};
    this.state.seq = this.state.seq || 0;
  }

  async rules() {
    let extra = [];
    try {
      if (await this.fs.exists('.vaultsyncignore')) {
        extra = parseIgnoreFile(new TextDecoder().decode(await this.fs.read('.vaultsyncignore')));
      }
    } catch (e) { /* no ignore file */ }
    return compileIgnore(ALWAYS_IGNORE.concat(extra));
  }

  async localHashes(rules) {
    const now = {};
    for (const f of await this.fs.list(rules)) {
      if (isIgnored(f.path, rules)) continue;
      const prev = this.state.files[f.path];
      if (prev && prev.size === f.size && prev.mtime === f.mtime) { now[f.path] = { hash: prev.hash, size: f.size, mtime: f.mtime }; continue; }
      now[f.path] = { hash: await gitHash(await this.fs.read(f.path)), size: f.size, mtime: f.mtime };
    }
    return now;
  }

  async sync() {
    const st = { up: 0, down: 0, delLocal: 0, delRemote: 0, merged: 0, conflicts: [] };
    const rules = await this.rules();
    const local = await this.localHashes(rules);
    const first = !this.state.initialized;
    const feed = await this.api.changes(first ? 0 : this.state.seq);
    const remote = {};
    for (const c of feed.changes.sort((x, y) => x.seq - y.seq)) remote[c.path] = c.deleted ? null : c.hash;

    const paths = new Set([...Object.keys(local), ...Object.keys(this.state.files), ...Object.keys(remote)]);
    const plan = [];
    for (const p of paths) {
      if (isIgnored(p, rules)) continue;
      const L = local[p] ? local[p].hash : null;
      const base = this.state.files[p] ? this.state.files[p].hash : null;
      if (first) {
        const R = p in remote ? remote[p] : null;
        if (L && R) plan.push(L === R ? ['record', p] : ['upload', p, null]);
        else if (L) plan.push(['upload', p, null]);
        else if (R) plan.push(['download', p]);
        continue;
      }
      const R = p in remote ? remote[p] : base;
      const localChanged = L !== base;
      const remoteChanged = R !== base;
      if (!localChanged && !remoteChanged) continue;
      if (L === R) { plan.push(L ? ['record', p] : ['forget', p]); continue; }
      if (!localChanged) plan.push(R ? ['download', p] : ['deleteLocal', p]);
      else if (!remoteChanged) plan.push(L ? ['upload', p, base] : ['deleteRemote', p, base]);
      else if (!L) plan.push(['download', p]);            // deleted here, changed there: bring it back
      else if (!R) plan.push(['upload', p, null]);        // deleted there, changed here: keep the edit
      else plan.push(['upload', p, base]);                // both changed: server merges or makes a copy
    }

    const deletions = plan.filter((x) => x[0] === 'deleteLocal' || x[0] === 'deleteRemote');
    if (deletions.length > MASS_DELETE) {
      const ok = await this.confirm(deletions.length, deletions.slice(0, 10).map((x) => x[1]));
      if (!ok) throw new Error(`stopped: ${deletions.length} deletions not confirmed`);
    }

    const recordLocal = async (p, hash) => {
      const f = local[p] || {};
      this.state.files[p] = { hash, size: f.size, mtime: f.mtime };
    };
    const download = async (p) => {
      const r = await this.api.get(p);
      if (!r) { // gone on the server meanwhile
        if (await this.fs.exists(p)) await this.fs.remove(p);
        delete this.state.files[p];
        return;
      }
      const s = await this.fs.write(p, r.data);
      this.state.files[p] = { hash: r.hash, size: s.size, mtime: s.mtime };
      st.down++;
    };

    await pool(plan, PARALLEL, async ([op, p, base]) => {
      try {
        if (op === 'record') await recordLocal(p, local[p].hash);
        else if (op === 'forget') delete this.state.files[p];
        else if (op === 'download') await download(p);
        else if (op === 'deleteLocal') {
          if (await this.fs.exists(p)) await this.fs.remove(p);
          delete this.state.files[p]; st.delLocal++;
        } else if (op === 'deleteRemote') {
          const r = await this.api.del(p, base);
          if (r.status === 'kept') await download(p); else { delete this.state.files[p]; st.delRemote++; }
        } else if (op === 'upload') {
          const data = await this.fs.read(p);
          const hash = await gitHash(data);
          const r = await this.api.put(p, data, base, hash);
          if (r.status === 'ok') { await recordLocal(p, hash); st.up++; }
          else {
            if (r.status === 'merged') st.merged++;
            if (r.status === 'conflict') { st.conflicts.push(r.copy); await download(r.copy); }
            await download(p);
          }
        }
      } catch (e) {
        this.log(`sync ${op} ${p} failed: ${e.message || e}`);
        throw e;
      }
    });

    this.state.seq = feed.seq;
    this.state.initialized = true;
    await this.save();
    return st;
  }
}

// ---------- Obsidian side ----------

const NFC = (s) => s.normalize('NFC');

class ObsidianFS {
  constructor(app) { this.app = app; this.adapter = app.vault.adapter; this.real = {}; }

  hidden(path) { return path.split('/').some((part) => part.startsWith('.')); }

  async list(rules) {
    const out = [];
    const walk = async (dir) => {
      const { files, folders } = await this.adapter.list(dir);
      for (const f of files) {
        const p = NFC(f);
        if (isIgnored(p, rules)) continue;
        const s = await this.adapter.stat(f);
        if (!s || s.type !== 'file') continue;
        this.real[p] = f;
        out.push({ path: p, size: s.size, mtime: s.mtime });
      }
      for (const d of folders) {
        if (isIgnored(NFC(d) + '/x', rules)) continue;
        await walk(d);
      }
    };
    await walk('');
    return out;
  }

  path(p) { return this.real[p] || p; }

  async exists(p) { return this.adapter.exists(this.path(p)); }

  async read(p) { return this.adapter.readBinary(this.path(p)); }

  async mkdirs(p) {
    const parts = p.split('/').slice(0, -1);
    for (let i = 1; i <= parts.length; i++) {
      const d = parts.slice(0, i).join('/');
      if (!(await this.adapter.exists(d))) {
        if (this.hidden(d)) await this.adapter.mkdir(d);
        else await this.app.vault.createFolder(d).catch(() => this.adapter.mkdir(d));
      }
    }
  }

  async write(p, data) {
    const real = this.path(p);
    await this.mkdirs(real);
    // Visible files go through the vault API so Obsidian (especially on iOS) sees them at once.
    const tf = this.hidden(real) ? null : this.app.vault.getAbstractFileByPath(real);
    if (tf instanceof TFile) await this.app.vault.modifyBinary(tf, data);
    else if (!this.hidden(real)) await this.app.vault.createBinary(real, data);
    else await this.adapter.writeBinary(real, data);
    this.real[p] = real;
    const s = await this.adapter.stat(real);
    return { size: s.size, mtime: s.mtime };
  }

  async remove(p) {
    const real = this.path(p);
    const tf = this.hidden(real) ? null : this.app.vault.getAbstractFileByPath(real);
    if (tf) await this.app.vault.delete(tf, true);
    else await this.adapter.remove(real);
    delete this.real[p];
    // drop folders the delete left empty
    let dir = real.split('/').slice(0, -1).join('/');
    while (dir) {
      const { files, folders } = await this.adapter.list(dir);
      if (files.length || folders.length) break;
      const tfd = this.app.vault.getAbstractFileByPath(dir);
      if (tfd instanceof TFolder) await this.app.vault.delete(tfd, true); else await this.adapter.rmdir(dir, false);
      dir = dir.split('/').slice(0, -1).join('/');
    }
  }
}

class ServerAPI {
  constructor(plugin) { this.plugin = plugin; }

  url(route, q) {
    const s = this.plugin.settings;
    const params = new URLSearchParams({ ...q, device: s.device });
    return s.server.replace(/\/+$/, '') + route + '?' + params.toString();
  }

  async req(route, q, opts = {}) {
    const r = await requestUrl({ url: this.url(route, q), method: opts.method || 'GET', body: opts.body,
      contentType: opts.body ? 'application/octet-stream' : undefined, throw: false });
    if (r.status === 404 && opts.allow404) return null;
    if (r.status >= 400) {
      let msg = `HTTP ${r.status}`;
      try { msg += ': ' + (r.json.error || ''); } catch (e) { /* not json */ }
      throw new Error(msg);
    }
    return r;
  }

  async ping() { return (await this.req('/api/ping', {})).json; }
  async changes(since) { return (await this.req('/api/changes', { since: String(since) })).json; }
  async get(path) {
    const r = await this.req('/api/file', { path }, { allow404: true });
    if (!r) return null;
    const h = Object.entries(r.headers || {}).find(([k]) => k.toLowerCase() === 'x-hash');
    const data = r.arrayBuffer;
    return { data, hash: h ? h[1] : await gitHash(data) };
  }
  async put(path, data, base, hash) {
    return (await this.req('/api/file', { path, base: base || '', hash }, { method: 'POST', body: data })).json;
  }
  async del(path, base) {
    return (await this.req('/api/delete', { path, base: base || '' }, { method: 'POST', body: new ArrayBuffer(0) })).json;
  }
}

class ConfirmModal extends (Modal || class {}) {
  constructor(app, count, sample, resolve) { super(app); Object.assign(this, { count, sample, resolve, done: false }); }
  onOpen() {
    const { contentEl } = this;
    contentEl.createEl('h3', { text: 'Vault Sync: confirm deletions' });
    contentEl.createEl('p', { text: `This sync would delete ${this.count} files. If you didn't just delete these on purpose, cancel.` });
    const ul = contentEl.createEl('ul');
    this.sample.forEach((p) => ul.createEl('li', { text: p }));
    new Setting(contentEl)
      .addButton((b) => b.setButtonText('Cancel').onClick(() => { this.done = true; this.resolve(false); this.close(); }))
      .addButton((b) => b.setButtonText('Delete them').setWarning().onClick(() => { this.done = true; this.resolve(true); this.close(); }));
  }
  onClose() { if (!this.done) this.resolve(false); this.contentEl.empty(); }
}

const DEFAULTS = { server: DEFAULT_SERVER, device: '', enabled: true, sync: { seq: 0, initialized: false, files: {} }, lastSync: 0, lastError: '' };

class VaultSyncPlugin extends (Plugin || class {}) {
  async onload() {
    this.settings = Object.assign({}, DEFAULTS, await this.loadData());
    if (!this.settings.device) {
      this.settings.device = Platform.isIosApp ? 'iPhone' : Platform.isAndroidApp ? 'Android' : Platform.isMacOS ? 'Mac' : 'PC';
      await this.saveData(this.settings);
    }
    this.running = false;
    this.again = false;
    this.status = this.addStatusBarItem();
    this.status.addClass('mod-clickable');
    this.status.onclick = () => this.syncNow(true);
    this.addRibbonIcon('refresh-cw', 'Vault Sync: sync now', () => this.syncNow(true));
    this.addCommand({ id: 'sync-now', name: 'Sync now', callback: () => this.syncNow(true) });
    this.addSettingTab(new VaultSyncSettings(this.app, this));
    this.paint();

    const soon = debounce(() => this.syncNow(false), EDIT_DELAY_MS, true);
    this.app.workspace.onLayoutReady(() => {
      for (const ev of ['create', 'modify', 'delete', 'rename']) this.registerEvent(this.app.vault.on(ev, () => { if (!this.applying) soon(); }));
      window.setTimeout(() => this.syncNow(false), 2000);
    });
    this.registerInterval(window.setInterval(() => this.syncNow(false), INTERVAL_MIN * 60 * 1000));
    this.registerDomEvent(document, 'visibilitychange', () => { if (document.visibilityState === 'visible') this.syncNow(false); });
  }

  paint(text) {
    const s = this.settings;
    let t = text;
    if (!t) {
      if (!s.enabled) t = 'Sync off';
      else if (s.lastError) t = 'Sync error';
      else if (s.lastSync) t = 'Synced ' + window.moment(s.lastSync).format('HH:mm');
      else t = 'Not synced yet';
    }
    this.status.setText('⟳ ' + t);
    this.status.setAttr('aria-label', s.lastError ? s.lastError : 'Vault Sync: click to sync now');
  }

  async syncNow(manual) {
    if (!this.settings.enabled && !manual) return;
    if (this.running) { this.again = true; return; }
    this.running = true;
    this.paint('Syncing…');
    try {
      const engine = new SyncEngine({
        fs: this.fs || (this.fs = new ObsidianFS(this.app)),
        api: this.api || (this.api = new ServerAPI(this)),
        state: this.settings.sync,
        save: () => this.saveData(this.settings),
        confirm: (count, sample) => new Promise((resolve) => new ConfirmModal(this.app, count, sample, resolve).open()),
        log: (m) => console.log('[vault-sync] ' + m),
      });
      this.applying = true;
      const r = await engine.sync();
      this.settings.lastSync = Date.now();
      this.settings.lastError = '';
      await this.saveData(this.settings);
      const moved = r.up + r.down + r.delLocal + r.delRemote;
      if (r.conflicts.length) new Notice(`Vault Sync: ${r.conflicts.length} conflict${r.conflicts.length > 1 ? 's' : ''}; both versions kept:\n${r.conflicts.join('\n')}`, 15000);
      else if (manual) new Notice(moved ? `Vault Sync: ↑${r.up} ↓${r.down}${r.delLocal + r.delRemote ? ` ✕${r.delLocal + r.delRemote}` : ''}${r.merged ? `, ${r.merged} merged` : ''}` : 'Vault Sync: up to date');
    } catch (e) {
      const msg = (e && e.message) || String(e);
      if (msg !== this.settings.lastError || manual) new Notice('Vault Sync: ' + msg + (/network|ERR_|failed to fetch|timed out|Load failed/i.test(msg) ? '\nIs Tailscale connected?' : ''), 10000);
      this.settings.lastError = msg;
      await this.saveData(this.settings);
    } finally {
      window.setTimeout(() => { this.applying = false; }, 500);
      this.running = false;
      this.paint();
      if (this.again) { this.again = false; window.setTimeout(() => this.syncNow(false), 1000); }
    }
  }
}

class VaultSyncSettings extends (PluginSettingTab || class {}) {
  constructor(app, plugin) { super(app, plugin); this.plugin = plugin; }
  display() {
    const { containerEl } = this;
    const p = this.plugin;
    const s = p.settings;
    containerEl.empty();
    new Setting(containerEl).setName('Sync').setDesc('Sync this vault with the Vault Sync server (needs Tailscale connected).')
      .addToggle((t) => t.setValue(s.enabled).onChange(async (v) => { s.enabled = v; await p.saveData(s); p.paint(); }));
    new Setting(containerEl).setName('Device name').setDesc('Shown in commit messages and conflict copies. Give each device its own (e.g. Mac, PC, iPhone 15).')
      .addText((t) => t.setValue(s.device).onChange(async (v) => { s.device = v.trim() || s.device; await p.saveData(s); }));
    new Setting(containerEl).setName('Server').setDesc('Address of the Vault Sync server on the tailnet.')
      .addText((t) => t.setValue(s.server).onChange(async (v) => { s.server = v.trim(); await p.saveData(s); }));
    const info = s.lastError ? `Last error: ${s.lastError}` : s.lastSync ? `Last sync ${window.moment(s.lastSync).fromNow()}, ${Object.keys(s.sync.files || {}).length} files tracked.` : 'Not synced yet.';
    new Setting(containerEl).setName('Status').setDesc(info)
      .addButton((b) => b.setButtonText('Test connection').onClick(async () => {
        try { const r = await (p.api || (p.api = new ServerAPI(p))).ping(); new Notice(`Vault Sync: connected as ${r.user} (server ${r.version})`); }
        catch (e) { new Notice('Vault Sync: ' + e.message + '\nIs Tailscale connected?', 8000); }
      }))
      .addButton((b) => b.setButtonText('Sync now').setCta().onClick(async () => { await p.syncNow(true); this.display(); }));
    new Setting(containerEl).setName('Start over').setDesc('Forget what this device last synced and compare everything again. Nothing is deleted; differences become uploads, downloads or conflict copies.')
      .addButton((b) => b.setButtonText('Reset sync state').onClick(async () => { s.sync = { seq: 0, initialized: false, files: {} }; await p.saveData(s); new Notice('Vault Sync: state reset; next sync compares everything.'); this.display(); }));
  }
}

module.exports = VaultSyncPlugin;
module.exports.SyncEngine = SyncEngine;
module.exports.gitHash = gitHash;
module.exports.sha1js = sha1js;
module.exports.compileIgnore = compileIgnore;
module.exports.isIgnored = isIgnored;
