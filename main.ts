// main.ts is mend, the CLI SPEC.md specifies. It implements the whole of SPEC.md: the command line, the output and
// exit codes, safe paths and format detection (sections 1 to 4), three-tier line matching (section 5), unified
// diffs (section 6), SEARCH/REPLACE blocks (section 7), V4A patches (section 8), JSON edits (section 9) and the
// all-or-nothing write (section 10). Node 22, the standard library alone; run it as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to runner.ts
// (the last lines below): keep that hand-over and runner.ts as they are.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  /** Move edits that succeeded, as [old path, new path], for the `R` lines of section 2. */
  readonly moves: [string, string][] = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

/** A file as lines: its own line break, its lines, and whether it ends with a line break (section 3). */
interface FileModel {
  br: string;
  lines: string[];
  finalBreak: boolean;
}

function parseFile(text: string): FileModel {
  if (text === '') return { br: '\n', lines: [], finalBreak: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const lines = text.split(br);
  const finalBreak = text.endsWith(br);
  if (finalBreak) lines.pop();
  return { br, lines, finalBreak };
}

function renderFile(m: FileModel): string {
  if (m.lines.length === 0) return '';
  return m.lines.join(m.br) + (m.finalBreak ? m.br : '');
}

/** One body line of a unified hunk or a V4A chunk: kind is ' ' (context), '-', '+' or '\\' (unified only). */
interface BodyItem {
  kind: string;
  text: string;
}

const leadWS = (s: string): string => /^[ \t]*/.exec(s)![0];
const stripTrailWS = (s: string): string => s.replace(/[ \t]+$/, '');
const stripBothWS = (s: string): string => stripTrailWS(s.replace(/^[ \t]+/, ''));

function tierNorm(tier: number, s: string): string {
  return tier === 0 ? s : tier === 1 ? stripTrailWS(s) : stripBothWS(s);
}

interface Occurrence {
  tier: number;
  positions: number[];
}

/**
 * Every occurrence of O in `lines` at the first tier where O occurs at least once (section 5), at or after `from`;
 * with `eofOnly`, only occurrences that end at the file's last line count. Null when O occurs at no tier.
 */
function findOcc(lines: string[], O: string[], strict: boolean, from = 0, eofOnly = false): Occurrence | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const tier of tiers) {
    // The file's lines are normalized once per tier, not once per candidate position: with a long file and a
    // long O the naive shape is quadratic in the file's size, and a check gives a run only 10 seconds.
    const nl = lines.map((s) => tierNorm(tier, s));
    const no = O.map((s) => tierNorm(tier, s));
    const positions: number[] = [];
    for (let i = from; i + O.length <= lines.length; i += 1) {
      if (eofOnly && i + O.length !== lines.length) continue;
      let ok = true;
      for (let k = 0; k < O.length; k += 1) {
        if (nl[i + k] !== no[k]) {
          ok = false;
          break;
        }
      }
      if (ok) positions.push(i);
    }
    if (positions.length > 0) return { tier, positions };
  }
  return null;
}

/**
 * The lines a match writes (section 5): context lines are the file's own matched lines; at tier 2 every other new
 * line that starts with the old first line's indent P has that indent replaced by the file's first matched line's
 * indent F.
 */
function buildN(fileLines: string[], pos: number, items: BodyItem[], tier: number, oTexts: string[]): string[] {
  const out: string[] = [];
  const F = tier === 2 ? leadWS(fileLines[pos]!) : '';
  const P = tier === 2 ? leadWS(oTexts[0]!) : '';
  let oi = 0;
  for (const it of items) {
    if (it.kind === ' ') {
      out.push(fileLines[pos + oi]!);
      oi += 1;
    } else if (it.kind === '-') {
      oi += 1;
    } else if (it.kind === '+') {
      let t = it.text;
      if (tier === 2 && t !== '' && t.trim() !== '' && t.startsWith(P)) t = F + t.slice(P.length);
      out.push(t);
    }
  }
  return out;
}

/** Whether a `\` line follows the last body line of one of the given kinds (the no-newline marker, section 6). */
function backslashAfter(items: BodyItem[], kinds: string[]): boolean {
  for (let k = items.length - 1; k >= 0; k -= 1) {
    if (kinds.includes(items[k]!.kind)) return items[k + 1]?.kind === '\\';
  }
  return false;
}

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

// ---------------------------------------------------------------- unified diffs (section 6)

interface Hunk {
  a: number;
  items: BodyItem[];
}

interface Section {
  gitOld: string | undefined;
  gitNew: string | undefined;
  pairOld: string | undefined;
  pairNew: string | undefined;
  renameFrom: string | undefined;
  renameTo: string | undefined;
  newFile: boolean;
  deletedFile: boolean;
  hunks: Hunk[];
  headerDone: boolean;
}

/** The path a `--- ` or `+++ ` line names: after the four characters, up to the first tab, spaces removed, a/ or b/ off. */
function pairPath(line: string): string {
  let rest = line.slice(4);
  const tab = rest.indexOf('\t');
  if (tab >= 0) rest = rest.slice(0, tab);
  rest = rest.trim();
  if (rest.startsWith('a/') || rest.startsWith('b/')) rest = rest.slice(2);
  return rest;
}

/** A raw header path as an edit path: `/dev/null` becomes null, an unnamed side stays undefined. */
function devNull(p: string | undefined): string | null | undefined {
  return p === undefined ? undefined : p === '/dev/null' ? null : p;
}

function sectionPaths(sec: Section): { oldP: string | null; newP: string | null } {
  let oldP = devNull(sec.pairOld);
  if (oldP === undefined) oldP = sec.renameFrom !== undefined ? sec.renameFrom : devNull(sec.gitOld);
  let newP = devNull(sec.pairNew);
  if (newP === undefined) newP = sec.renameTo !== undefined ? sec.renameTo : devNull(sec.gitNew);
  return { oldP: oldP ?? null, newP: newP ?? null };
}

function applyHunks(model: FileModel, hunks: Hunk[], strict: boolean, path: string): void {
  let d = 0;
  for (const h of hunks) {
    const oTexts: string[] = [];
    let nCount = 0;
    for (const it of h.items) {
      if (it.kind === ' ' || it.kind === '-') oTexts.push(it.text);
      if (it.kind === ' ' || it.kind === '+') nCount += 1;
    }
    if (oTexts.length > 0) {
      const occ = findOcc(model.lines, oTexts, strict);
      if (occ === null) throw new Fail('no-match', path);
      const target = h.a - 1 + d;
      let pos = occ.positions[0]!;
      let best = Math.abs(pos - target);
      for (const p of occ.positions) {
        const dist = Math.abs(p - target);
        if (dist < best) {
          best = dist;
          pos = p;
        }
      }
      const runsToEnd = pos + oTexts.length === model.lines.length;
      const repl = buildN(model.lines, pos, h.items, occ.tier, oTexts);
      model.lines.splice(pos, oTexts.length, ...repl);
      if (runsToEnd) model.finalBreak = !backslashAfter(h.items, [' ', '+']);
      d += nCount - oTexts.length;
    } else {
      let idx = h.a + d;
      if (idx < 0) idx = 0;
      if (idx > model.lines.length) idx = model.lines.length;
      const atEnd = idx === model.lines.length;
      const add = h.items.filter((it) => it.kind === '+').map((it) => it.text);
      model.lines.splice(idx, 0, ...add);
      if (atEnd) model.finalBreak = !backslashAfter(h.items, [' ', '+']);
      d += add.length;
    }
  }
}

function unifiedSectionEdit(sec: Section, strict: boolean): Edit {
  return (tree) => {
    const { oldP, newP } = sectionPaths(sec);
    if (oldP === null || sec.newFile) {
      // A creation: the new path does not exist; the file is the `+` lines of all its hunks.
      const p = newP ?? '/dev/null';
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      const plus: string[] = [];
      for (const h of sec.hunks) for (const it of h.items) if (it.kind === '+') plus.push(it.text);
      let finalBreak = true;
      for (let hi = sec.hunks.length - 1; hi >= 0; hi -= 1) {
        const items = sec.hunks[hi]!.items;
        if (items.some((it) => it.kind === '+')) {
          finalBreak = !backslashAfter(items, ['+']);
          break;
        }
      }
      tree.now.set(p, plus.length === 0 ? '' : plus.join('\n') + (finalBreak ? '\n' : ''));
      return;
    }
    if (newP === null || sec.deletedFile) {
      // A deletion: the old path exists; it is deleted, and its hunks are not read.
      if (!safe(oldP)) throw new Fail('unsafe', oldP);
      if (tree.get(oldP) === null) throw new Fail('missing', oldP);
      tree.now.set(oldP, null);
      return;
    }
    if (!safe(oldP)) throw new Fail('unsafe', oldP);
    if (newP !== oldP && !safe(newP)) throw new Fail('unsafe', newP);
    const text = tree.get(oldP);
    if (text === null) throw new Fail('missing', oldP);
    if (newP !== oldP && tree.get(newP) !== null) throw new Fail('exists', newP);
    const model = parseFile(text);
    applyHunks(model, sec.hunks, strict, oldP);
    tree.now.set(newP, renderFile(model));
    if (newP !== oldP) {
      tree.now.set(oldP, null);
      tree.moves.push([oldP, newP]);
    }
  };
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections: Section[] = [];
  let cur: Section | null = null;
  const newSection = (): Section => {
    const s: Section = {
      gitOld: undefined,
      gitNew: undefined,
      pairOld: undefined,
      pairNew: undefined,
      renameFrom: undefined,
      renameTo: undefined,
      newFile: false,
      deletedFile: false,
      hunks: [],
      headerDone: false,
    };
    sections.push(s);
    return s;
  };
  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(.*) b\/(.*)$/.exec(line);
      if (m === null || m[1] === '' || m[2] === '') throw new Exit2(`error: parse ${i + 1}`);
      cur = newSection();
      cur.gitOld = m[1]!;
      cur.gitNew = m[2]!;
      i += 1;
    } else if (line.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const hm = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(line);
      if (hm === null) throw new Exit2(`error: parse ${i + 1}`);
      // The hunk's body: lines starting with ' ', '-', '+' or '\', or empty; it ends at the first other line, at a
      // `diff --git ` line or at a `--- ` line followed by a `+++ ` line. Empty lines at its end are not part of it.
      const raw: { item: BodyItem; emptyLine: boolean }[] = [];
      let j = i + 1;
      while (j < lines.length) {
        const l = lines[j]!;
        if (l.startsWith('diff --git ')) break;
        if (l.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
        if (l === '') {
          raw.push({ item: { kind: ' ', text: '' }, emptyLine: true });
          j += 1;
        } else if (l[0] === ' ' || l[0] === '-' || l[0] === '+' || l[0] === '\\') {
          raw.push({ item: { kind: l[0]!, text: l.slice(1) }, emptyLine: false });
          j += 1;
        } else break;
      }
      while (raw.length > 0 && raw[raw.length - 1]!.emptyLine) raw.pop();
      cur.hunks.push({ a: Number(hm[1]!), items: raw.map((r) => r.item) });
      cur.headerDone = true;
      i = j;
    } else if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (cur === null || cur.headerDone || cur.pairOld !== undefined) cur = newSection();
      cur.pairOld = pairPath(line);
      cur.pairNew = pairPath(lines[i + 1]!);
      i += 2;
    } else if (line.startsWith('--- ') && cur !== null && !cur.headerDone) {
      // A `--- ` line inside a section's header that no `+++ ` line follows.
      throw new Exit2(`error: parse ${i + 2}`);
    } else if (cur !== null && !cur.headerDone) {
      if (line.startsWith('rename from ')) cur.renameFrom = line.slice('rename from '.length).trim();
      else if (line.startsWith('rename to ')) cur.renameTo = line.slice('rename to '.length).trim();
      else if (line.startsWith('new file mode')) cur.newFile = true;
      else if (line.startsWith('deleted file mode')) cur.deletedFile = true;
      i += 1;
    } else {
      // Outside bodies, lines that are not part of a section header are ignored (prose, code fences).
      i += 1;
    }
  }
  return sections.map((s) => unifiedSectionEdit(s, strict));
}

// ---------------------------------------------------------------- SEARCH/REPLACE blocks (section 7)

interface SRBlock {
  path: string;
  oldLines: string[];
  newLines: string[];
}

function srBlockEdit(b: SRBlock, strict: boolean): Edit {
  return (tree) => {
    const p = b.path;
    if (!safe(p)) throw new Fail('unsafe', p);
    if (b.oldLines.length === 0) {
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, b.newLines.length === 0 ? '' : b.newLines.join('\n') + '\n');
      return;
    }
    const text = tree.get(p);
    if (text === null) throw new Fail('missing', p);
    const model = parseFile(text);
    const occ = findOcc(model.lines, b.oldLines, strict);
    if (occ === null) throw new Fail('no-match', p);
    if (occ.positions.length > 1) throw new Fail('ambiguous', p);
    const pos = occ.positions[0]!;
    const items = b.newLines.map((t) => ({ kind: '+', text: t }));
    const repl = buildN(model.lines, pos, items, occ.tier, b.oldLines);
    model.lines.splice(pos, b.oldLines.length, ...repl);
    tree.now.set(p, renderFile(model));
  };
}

function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const blocks: SRBlock[] = [];
  let prevEnd = -1;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i += 1;
      continue;
    }
    const s = i;
    let m = -1;
    for (let j = s + 1; j < lines.length; j += 1) {
      if (lines[j]!.trimEnd() === '=======') {
        m = j;
        break;
      }
    }
    let e = -1;
    if (m >= 0) {
      for (let j = m + 1; j < lines.length; j += 1) {
        if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
          e = j;
          break;
        }
      }
    }
    if (m < 0 || e < 0) throw new Exit2(`error: parse ${s + 1}`);
    // The path: the nearest line before the SEARCH line, after the previous block, that is not blank and does not
    // start with three backticks once its surrounding whitespace is removed.
    let path: string | null = null;
    for (let j = s - 1; j > prevEnd; j -= 1) {
      const t = lines[j]!.trim();
      if (t === '' || t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${s + 1}`);
      path = prevPath;
    }
    blocks.push({ path, oldLines: lines.slice(s + 1, m), newLines: lines.slice(m + 1, e) });
    prevPath = path;
    prevEnd = e;
    i = e + 1;
  }
  return blocks.map((b) => srBlockEdit(b, strict));
}

// ---------------------------------------------------------------- V4A patches (section 8)

interface VChunk {
  anchor: string | null;
  items: BodyItem[];
  eof: boolean;
}

interface VSection {
  kind: 'add' | 'delete' | 'update';
  path: string;
  headerLine: number;
  addLines: string[];
  moveTo: string | null;
  chunks: VChunk[];
}

function applyChunks(model: FileModel, chunks: VChunk[], strict: boolean, path: string): void {
  let cursor = 0;
  const tiers = strict ? [0] : [0, 1, 2];
  for (const ch of chunks) {
    if (ch.anchor !== null) {
      let found = -1;
      for (const tier of tiers) {
        const want = tierNorm(tier, ch.anchor);
        for (let k = cursor; k < model.lines.length; k += 1) {
          if (tierNorm(tier, model.lines[k]!) === want) {
            found = k;
            break;
          }
        }
        if (found >= 0) break;
      }
      if (found < 0) throw new Fail('no-match', path);
      cursor = found + 1;
    }
    const oTexts: string[] = [];
    for (const it of ch.items) if (it.kind === ' ' || it.kind === '-') oTexts.push(it.text);
    if (oTexts.length === 0) {
      const at = ch.eof ? model.lines.length : Math.min(cursor, model.lines.length);
      const add = ch.items.filter((it) => it.kind === '+').map((it) => it.text);
      model.lines.splice(at, 0, ...add);
      cursor = at + add.length;
    } else {
      const occ = findOcc(model.lines, oTexts, strict, cursor, ch.eof);
      if (occ === null) throw new Fail('no-match', path);
      const pos = occ.positions[0]!;
      const repl = buildN(model.lines, pos, ch.items, occ.tier, oTexts);
      model.lines.splice(pos, oTexts.length, ...repl);
      cursor = pos + repl.length;
    }
  }
}

function v4aSectionEdit(sec: VSection, strict: boolean): Edit {
  return (tree) => {
    const p = sec.path;
    if (sec.kind === 'add') {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, sec.addLines.length === 0 ? '' : sec.addLines.join('\n') + '\n');
      return;
    }
    if (sec.kind === 'delete') {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) === null) throw new Fail('missing', p);
      tree.now.set(p, null);
      return;
    }
    if (!safe(p)) throw new Fail('unsafe', p);
    if (sec.moveTo !== null && !safe(sec.moveTo)) throw new Fail('unsafe', sec.moveTo);
    const text = tree.get(p);
    if (text === null) throw new Fail('missing', p);
    if (sec.moveTo !== null && tree.get(sec.moveTo) !== null) throw new Fail('exists', sec.moveTo);
    const model = parseFile(text);
    applyChunks(model, sec.chunks, strict, p);
    const dest = sec.moveTo ?? p;
    tree.now.set(dest, renderFile(model));
    if (sec.moveTo !== null) {
      tree.now.set(p, null);
      tree.moves.push([p, sec.moveTo]);
    }
  };
}

function parseVUpdate(sec: VSection, raw: { text: string; line: number }[]): void {
  let start = 0;
  if (raw.length > 0 && raw[0]!.text.startsWith('*** Move to:')) {
    sec.moveTo = raw[0]!.text.slice('*** Move to:'.length).trim();
    start = 1;
  }
  let cur: VChunk | null = null;
  let started = false;
  for (let k = start; k < raw.length; k += 1) {
    const { text, line } = raw[k]!;
    if (text.startsWith('@@')) {
      const anchorText = text.slice(2).trim();
      cur = { anchor: anchorText === '' ? null : anchorText, items: [], eof: false };
      sec.chunks.push(cur);
      started = true;
    } else if (text === '*** End of File') {
      if (cur === null) {
        cur = { anchor: null, items: [], eof: true };
        sec.chunks.push(cur);
        started = true;
      } else {
        cur.eof = true;
      }
      cur = null;
    } else if (text === '' || text[0] === ' ' || text[0] === '-' || text[0] === '+') {
      if (cur === null) {
        if (started) throw new Exit2(`error: parse ${line}`);
        cur = { anchor: null, items: [], eof: false };
        sec.chunks.push(cur);
        started = true;
      }
      cur.items.push(text === '' ? { kind: ' ', text: '' } : { kind: text[0]!, text: text.slice(1) });
    } else {
      throw new Exit2(`error: parse ${line}`);
    }
  }
  if (sec.chunks.length === 0 && sec.moveTo === null) throw new Exit2(`error: parse ${sec.headerLine}`);
}

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k -= 1) {
    if (!blank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const headerKind = (l: string): 'add' | 'delete' | 'update' | null =>
    l.startsWith('*** Add File:') ? 'add' : l.startsWith('*** Delete File:') ? 'delete' : l.startsWith('*** Update File:') ? 'update' : null;
  const sections: VSection[] = [];
  let i = first + 1;
  while (i < last) {
    const l = lines[i]!;
    if (blank(l)) {
      i += 1;
      continue;
    }
    const kind = headerKind(l);
    if (kind === null) throw new Exit2(`error: parse ${i + 1}`);
    const sec: VSection = { kind, path: l.slice(l.indexOf(':') + 1).trim(), headerLine: i + 1, addLines: [], moveTo: null, chunks: [] };
    // The section's lines run to the next section or to `*** End Patch`; blank lines at its end are not part of it.
    const raw: { text: string; line: number }[] = [];
    let j = i + 1;
    while (j < last && headerKind(lines[j]!) === null) {
      raw.push({ text: lines[j]!, line: j + 1 });
      j += 1;
    }
    while (raw.length > 0 && blank(raw[raw.length - 1]!.text)) raw.pop();
    if (kind === 'add') {
      for (const r of raw) {
        if (r.text.startsWith('+')) sec.addLines.push(r.text.slice(1));
        else if (r.text === '') sec.addLines.push('');
        else throw new Exit2(`error: parse ${r.line}`);
      }
    } else if (kind === 'delete') {
      if (raw.length > 0) throw new Exit2(`error: parse ${raw[0]!.line}`);
    } else {
      parseVUpdate(sec, raw);
    }
    sections.push(sec);
    i = j;
  }
  return sections.map((s) => v4aSectionEdit(s, strict));
}

// ---------------------------------------------------------------- JSON edits (section 9)

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---------------------------------------------------------------- the run (sections 1, 2 and 10)

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    edits =
      kind === 'json'
        ? jsonEdits(text, lines)
        : kind === 'unified'
          ? unifiedEdits(lines, strict)
          : kind === 'search-replace'
            ? searchReplaceEdits(lines, strict)
            : v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const movesBefore = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves.length = movesBefore;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  // The paths whose state changed, and the move pairs whose `R` line replaces a `D` and an `A` line (section 2).
  const finalOf = (p: string): string | null => (tree.now.has(p) ? tree.now.get(p)! : tree.original(p));
  const changed = [...tree.now.keys()].filter((p) => tree.original(p) !== tree.now.get(p));
  const seenPair = new Set<string>();
  const rPairs: [string, string][] = [];
  for (const [o, n] of tree.moves) {
    const key = `${o}\n${n}`;
    if (seenPair.has(key)) continue;
    seenPair.add(key);
    if (tree.original(o) !== null && finalOf(o) === null && tree.original(n) === null && finalOf(n) !== null) rPairs.push([o, n]);
  }
  const rOld = new Set(rPairs.map(([o]) => o));
  const rNew = new Set(rPairs.map(([, n]) => n));
  const rows: { key: string; text: string }[] = [];
  for (const [o, n] of rPairs) rows.push({ key: n, text: `R ${o} -> ${n}` });
  for (const p of changed) {
    if (rOld.has(p) || rNew.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    rows.push({ key: p, text: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((x, y) => Buffer.compare(Buffer.from(x.key), Buffer.from(y.key)));
  if (!check) {
    for (const p of changed) {
      const now = tree.now.get(p)!;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...rows.map((r) => r.text), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
