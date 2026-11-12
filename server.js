'use strict';
/*
  سيرفر مزامنة "مدارس الأحد" — Node.js 18+ بدون أي مكتبات خارجية.
  - حسابات (أمين خدمة / خادم) + كود دعوة + موافقة الأمين على الخدام
  - مزامنة بيانات الفصول والمخدومين والحضور والافتقاد والمنهج بين كل التليفونات
  - بيقدّم تطبيق الويب نفسه من مجلد public على نفس الرابط
*/
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = Number(process.env.PORT) || 3000;
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, 'data');
const FILE = path.join(DATA_DIR, 'db.json');
const PUBLIC = path.join(__dirname, 'public');
const MAX_BODY = 10 * 1024 * 1024;
const TOKEN_DAYS = 90;
const COLL = ['classes', 'members', 'follow', 'lessons', 'att'];

/* ---------- التخزين ---------- */
let db = { users: {}, services: {}, tokens: {} };
try { fs.mkdirSync(DATA_DIR, { recursive: true }); } catch (e) {}
try { db = Object.assign(db, JSON.parse(fs.readFileSync(FILE, 'utf8'))); } catch (e) { /* أول تشغيل */ }

let flushTimer = null;
function save() {
  if (flushTimer) return;
  flushTimer = setTimeout(() => {
    flushTimer = null;
    const tmp = FILE + '.tmp';
    try { fs.writeFileSync(tmp, JSON.stringify(db)); fs.renameSync(tmp, FILE); }
    catch (e) { console.error('تعذّر حفظ البيانات:', e.message); }
  }, 300);
}
process.on('SIGTERM', () => { try { fs.writeFileSync(FILE, JSON.stringify(db)); } catch (e) {} process.exit(0); });
process.on('SIGINT', () => { try { fs.writeFileSync(FILE, JSON.stringify(db)); } catch (e) {} process.exit(0); });

/* ---------- أدوات ---------- */
const rid = (n = 16) => crypto.randomBytes(n).toString('hex');
const ALPHA = 'ABCDEFGHJKMNPQRSTUVWXYZ23456789';
function newInvite() {
  let c;
  do { c = Array.from(crypto.randomBytes(6), b => ALPHA[b % ALPHA.length]).join(''); }
  while (Object.values(db.services).some(s => s.invite === c));
  return c;
}
function hashPw(pw, salt) { return crypto.scryptSync(pw, salt, 64).toString('hex'); }
function checkPw(pw, u) {
  const a = Buffer.from(hashPw(pw, u.salt), 'hex'), b = Buffer.from(u.hash, 'hex');
  return a.length === b.length && crypto.timingSafeEqual(a, b);
}
const tokHash = t => crypto.createHash('sha256').update(t).digest('hex');
function issueToken(userKey) {
  const t = rid(32);
  db.tokens[tokHash(t)] = { u: userKey, exp: Date.now() + TOKEN_DAYS * 864e5 };
  save();
  return t;
}
function authUser(req) {
  const h = req.headers.authorization || '';
  const t = h.startsWith('Bearer ') ? h.slice(7) : '';
  if (!t) return null;
  const rec = db.tokens[tokHash(t)];
  if (!rec) return null;
  if (rec.exp < Date.now()) { delete db.tokens[tokHash(t)]; save(); return null; }
  const u = db.users[rec.u];
  if (!u || u.status !== 'active') return null;
  return { key: rec.u, user: u, svc: db.services[u.svcId], tok: tokHash(t) };
}
function revokeUserTokens(userKey) {
  for (const k of Object.keys(db.tokens)) if (db.tokens[k].u === userKey) delete db.tokens[k];
}
const validName = s => typeof s === 'string' && /^[A-Za-z0-9_.\u0600-\u06FF]{3,30}$/.test(s);
const validPw = s => typeof s === 'string' && s.length >= 6 && s.length <= 100;
const str = (v, n) => String(v == null ? '' : v).slice(0, n);

/* تقييد محاولات الدخول الغلط */
const fails = new Map();
function ipOf(req) { return String(req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0].trim(); }
function locked(k) { const f = fails.get(k); return f && f.n >= 8 && Date.now() - f.t < 10 * 60e3; }
function fail(k) { const f = fails.get(k) || { n: 0, t: 0 }; if (Date.now() - f.t > 10 * 60e3) f.n = 0; f.n++; f.t = Date.now(); fails.set(k, f); }

/* ---------- تنظيف سجلات المزامنة ---------- */
function sanitize(c, r) {
  switch (c) {
    case 'classes': return { name: str(r.name, 60) };
    case 'members': return { name: str(r.name, 80), classId: str(r.classId, 40), phone: str(r.phone, 30), parent: str(r.parent, 30), address: str(r.address, 200), birth: str(r.birth, 10), notes: str(r.notes, 1000), created: str(r.created, 10) };
    case 'follow': return { memberId: str(r.memberId, 40), date: str(r.date, 10), note: str(r.note, 2000) };
    case 'lessons': return { title: str(r.title, 120), date: str(r.date, 10), classId: str(r.classId, 40), link: str(r.link, 500), notes: str(r.notes, 5000) };
    case 'att': return { d: str(r.d, 10), m: str(r.m, 40), v: r.v === 1 ? 1 : 0 };
  }
  return {};
}
function doSync(svc, body) {
  const since = Number(body.since) || 0;
  const ch = body.changes || {};
  for (const c of COLL) {
    const arr = ch[c];
    if (!Array.isArray(arr)) continue;
    const store = svc.records[c];
    for (const r of arr) {
      if (!r || typeof r.id !== 'string' || r.id.length > 90) continue;
      const u = Number(r._u) || 0;
      const ex = store[r.id];
      if (ex && ex._u > u) continue; // الأحدث يكسب
      const rec = r._d ? {} : sanitize(c, r);
      rec.id = r.id; rec._u = u; rec._s = ++svc.seq;
      if (r._d) rec._d = 1;
      store[r.id] = rec;
    }
  }
  const out = {};
  for (const c of COLL) out[c] = Object.values(svc.records[c]).filter(r => r._s > since);
  save();
  return { seq: svc.seq, changes: out };
}

/* ---------- HTTP ---------- */
const MIME = { '.html': 'text/html; charset=utf-8', '.png': 'image/png', '.svg': 'image/svg+xml', '.json': 'application/json', '.js': 'text/javascript', '.ico': 'image/x-icon', '.webmanifest': 'application/manifest+json' };
function send(res, code, obj) {
  const body = JSON.stringify(obj);
  res.writeHead(code, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' });
  res.end(body);
}
const err = (res, code, msg) => send(res, code, { error: msg });
function readBody(req) {
  return new Promise((resolve, reject) => {
    let size = 0; const chunks = [];
    req.on('data', d => { size += d.length; if (size > MAX_BODY) { reject(Object.assign(new Error('الطلب كبير جدًا'), { code: 413 })); req.destroy(); } else chunks.push(d); });
    req.on('end', () => { try { resolve(chunks.length ? JSON.parse(Buffer.concat(chunks).toString('utf8')) : {}); } catch (e) { reject(Object.assign(new Error('بيانات غير صالحة'), { code: 400 })); } });
    req.on('error', reject);
  });
}
const pubUser = a => ({ username: a.user.username, role: a.user.role });
const pubSvc = (a) => ({ id: a.svc.id, name: a.svc.name, invite: a.user.role === 'admin' ? a.svc.invite : null });

async function api(req, res, p) {
  const body = req.method === 'POST' ? await readBody(req) : {};

  if (p === '/api/health') return send(res, 200, { ok: true });

  if (p === '/api/register-service' && req.method === 'POST') {
    const { username, password, serviceName } = body;
    if (!validName(username)) return err(res, 400, 'اسم المستخدم لازم يكون من 3 لـ 30 حرف أو رقم بدون مسافات');
    if (!validPw(password)) return err(res, 400, 'كلمة السر لازم تكون 6 حروف على الأقل');
    const name = str(serviceName, 60).trim();
    if (!name) return err(res, 400, 'اكتب اسم الخدمة');
    const key = username.toLowerCase();
    if (db.users[key]) return err(res, 409, 'اسم المستخدم ده موجود، اختار اسم تاني');
    const svc = { id: rid(6), name, invite: newInvite(), seq: 0, created: Date.now(), records: { classes: {}, members: {}, follow: {}, lessons: {}, att: {} } };
    db.services[svc.id] = svc;
    const salt = rid(16);
    db.users[key] = { username, salt, hash: hashPw(password, salt), svcId: svc.id, role: 'admin', status: 'active', created: Date.now() };
    const token = issueToken(key);
    save();
    const a = { user: db.users[key], svc };
    return send(res, 200, { token, user: pubUser(a), service: pubSvc(a) });
  }

  if (p === '/api/join' && req.method === 'POST') {
    const { username, password, code } = body;
    if (!validName(username)) return err(res, 400, 'اسم المستخدم لازم يكون من 3 لـ 30 حرف أو رقم بدون مسافات');
    if (!validPw(password)) return err(res, 400, 'كلمة السر لازم تكون 6 حروف على الأقل');
    const svc = Object.values(db.services).find(s => s.invite === str(code, 12).trim().toUpperCase());
    if (!svc) return err(res, 404, 'كود الدعوة غلط');
    const key = username.toLowerCase();
    if (db.users[key]) return err(res, 409, 'اسم المستخدم ده موجود، اختار اسم تاني');
    const salt = rid(16);
    db.users[key] = { username, salt, hash: hashPw(password, salt), svcId: svc.id, role: 'servant', status: 'pending', created: Date.now() };
    save();
    return send(res, 200, { status: 'pending', serviceName: svc.name });
  }

  if (p === '/api/login' && req.method === 'POST') {
    const key = str(body.username, 30).toLowerCase();
    const lk = ipOf(req) + '|' + key;
    if (locked(lk)) return err(res, 429, 'محاولات كتير غلط. استنى 10 دقايق وجرّب تاني');
    const u = db.users[key];
    if (!u || !checkPw(String(body.password || ''), u)) { fail(lk); return err(res, 401, 'اسم المستخدم أو كلمة السر غلط'); }
    if (u.status === 'pending') return err(res, 403, 'حسابك في انتظار موافقة أمين الخدمة');
    if (u.status !== 'active') return err(res, 403, 'الحساب ده متوقف');
    fails.delete(lk);
    const token = issueToken(key);
    const a = { user: u, svc: db.services[u.svcId] };
    return send(res, 200, { token, user: pubUser(a), service: pubSvc(a) });
  }

  /* ---- من هنا محتاج تسجيل دخول ---- */
  const a = authUser(req);
  if (!a) return err(res, 401, 'لازم تسجل دخول');

  if (p === '/api/me') return send(res, 200, { user: pubUser(a), service: pubSvc(a) });

  if (p === '/api/logout' && req.method === 'POST') { delete db.tokens[a.tok]; save(); return send(res, 200, { ok: true }); }

  if (p === '/api/sync' && req.method === 'POST') return send(res, 200, doSync(a.svc, body));

  if (p === '/api/password' && req.method === 'POST') {
    if (!checkPw(String(body.old || ''), a.user)) return err(res, 403, 'كلمة السر الحالية غلط');
    if (!validPw(body.new)) return err(res, 400, 'كلمة السر الجديدة لازم تكون 6 حروف على الأقل');
    a.user.salt = rid(16); a.user.hash = hashPw(body.new, a.user.salt);
    for (const k of Object.keys(db.tokens)) if (db.tokens[k].u === a.key && k !== a.tok) delete db.tokens[k];
    save();
    return send(res, 200, { ok: true });
  }

  /* ---- إدارة الخدام (أمين الخدمة فقط) ---- */
  if (p.startsWith('/api/users') || p === '/api/invite/reset') {
    if (a.user.role !== 'admin') return err(res, 403, 'ده متاح لأمين الخدمة فقط');
    if (p === '/api/users' && req.method === 'GET') {
      const list = Object.values(db.users).filter(u => u.svcId === a.svc.id).map(u => ({ username: u.username, role: u.role, status: u.status })).sort((x, y) => (x.status === 'pending' ? -1 : 1) - (y.status === 'pending' ? -1 : 1));
      return send(res, 200, { users: list, invite: a.svc.invite });
    }
    if (p === '/api/invite/reset' && req.method === 'POST') { a.svc.invite = newInvite(); save(); return send(res, 200, { invite: a.svc.invite }); }
    const m = p.match(/^\/api\/users\/(approve|remove|admin|servant)$/);
    if (m && req.method === 'POST') {
      const key = str(body.username, 30).toLowerCase();
      const t = db.users[key];
      if (!t || t.svcId !== a.svc.id) return err(res, 404, 'المستخدم غير موجود');
      if (key === a.key && m[1] !== 'approve') return err(res, 400, 'مينفعش تعدّل على حسابك من هنا');
      if (m[1] === 'approve') t.status = 'active';
      else if (m[1] === 'remove') { delete db.users[key]; revokeUserTokens(key); }
      else if (m[1] === 'admin') t.role = 'admin';
      else if (m[1] === 'servant') t.role = 'servant';
      save();
      return send(res, 200, { ok: true });
    }
  }

  return err(res, 404, 'غير موجود');
}

function serveStatic(req, res, p) {
  let f = p === '/' ? '/index.html' : p;
  f = path.normalize(f).replace(/^(\.\.[\/\\])+/, '');
  const full = path.join(PUBLIC, f);
  if (!full.startsWith(PUBLIC)) { res.writeHead(403); return res.end(); }
  fs.readFile(full, (e, data) => {
    if (e) { res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' }); return res.end('غير موجود'); }
    res.writeHead(200, { 'Content-Type': MIME[path.extname(full)] || 'application/octet-stream', 'Cache-Control': 'no-cache' });
    res.end(data);
  });
}

http.createServer(async (req, res) => {
  res.setHeader('Access-Control-Allow-Origin', '*');
  res.setHeader('Access-Control-Allow-Headers', 'Content-Type, Authorization');
  res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
  if (req.method === 'OPTIONS') { res.writeHead(204); return res.end(); }
  const p = new URL(req.url, 'http://x').pathname;
  try {
    if (p.startsWith('/api/')) await api(req, res, p);
    else serveStatic(req, res, p);
  } catch (e) {
    if (!res.headersSent) err(res, e.code || 500, e.code ? e.message : 'خطأ في السيرفر');
    if (!e.code) console.error(e);
  }
}).listen(PORT, () => console.log('السيرفر شغال على المنفذ ' + PORT + ' — البيانات في ' + FILE));
