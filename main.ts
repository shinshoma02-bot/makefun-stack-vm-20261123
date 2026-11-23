// tiny-stack-vm entry: runs make.fun's tiny stack ISA (ISA.md, version 1).
// For each /input/<id>: runs program.bin on input.bin, writes /output/<id>/stdout.bin and exit.txt.
// Rules follow generator/subject/vm.mjs in the order ISA.md gives them.
import { mkdirSync, readdirSync, readFileSync, writeFileSync, existsSync } from 'node:fs';
import { join } from 'node:path';

const STACK = 256, CALLS = 64, MEM = 256, STEPS = 1000000, OUTMAX = 65536;

// [opcode, immediate bytes, pops, pushes]
const OPS = [
  [0x00, 0, 0, 0], [0x01, 1, 0, 1], [0x02, 4, 0, 1], [0x03, 0, 1, 0], [0x04, 0, 1, 2], [0x05, 0, 2, 2],
  [0x06, 0, 2, 3], [0x07, 0, 3, 3], [0x10, 0, 2, 1], [0x11, 0, 2, 1], [0x12, 0, 2, 1], [0x13, 0, 2, 1],
  [0x14, 0, 2, 1], [0x15, 0, 2, 1], [0x16, 0, 2, 1], [0x17, 0, 1, 1], [0x18, 0, 2, 1], [0x19, 0, 2, 1],
  [0x1a, 0, 2, 1], [0x1b, 0, 1, 1], [0x1c, 0, 2, 1], [0x1d, 0, 2, 1], [0x1e, 0, 2, 1], [0x20, 0, 2, 1],
  [0x21, 0, 2, 1], [0x22, 0, 2, 1], [0x30, 2, 0, 0], [0x31, 2, 1, 0], [0x32, 2, 1, 0], [0x33, 2, 0, 0],
  [0x34, 0, 0, 0], [0x40, 0, 1, 1], [0x41, 0, 2, 0], [0x50, 0, 1, 0], [0x51, 0, 1, 0], [0x52, 0, 0, 1],
  [0x53, 0, 1, 0],
];
const IMM = new Int8Array(256).fill(-1), POPS = new Uint8Array(256), PUSHES = new Uint8Array(256);
for (const [op, imm, pops, pushes] of OPS) { IMM[op] = imm; POPS[op] = pops; PUSHES[op] = pushes; }

// Returns { out, exit }: the bytes written, and the exit code (EXIT's value, HALT's 0, or a trap's code).
function run(prog: Uint8Array, input: Uint8Array) {
  const n = prog.length;
  const D = new Int32Array(STACK), C = new Int32Array(CALLS), M = new Int32Array(MEM);
  const out = new Uint8Array(OUTMAX);
  let sp = 0, csp = 0, olen = 0, inPos = 0, pc = 0, steps = 0, exit = -1;

  while (exit < 0) {
    if (steps === STEPS) { exit = 10; break; }
    if (pc < 0 || pc >= n) { exit = 9; break; }
    const op = prog[pc], imm = IMM[op];
    if (imm < 0) { exit = 5; break; }
    if (pc + imm >= n) { exit = 9; break; }
    steps++;
    const next = pc + 1 + imm;
    if (sp < POPS[op]) { exit = 2; break; }
    if (sp - POPS[op] + PUSHES[op] > STACK) { exit = 3; break; }
    pc = next;
    // Operand helpers: a = second from top, b = top (for binary ops).
    const rel = (((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16);
    switch (op) {
      case 0x00: exit = 0; break;
      case 0x01: D[sp++] = (prog[next - 1] << 24) >> 24; break;
      case 0x02: D[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 0x10: D[sp - 2] = (D[sp - 2] + D[sp - 1]) | 0; sp--; break;
      case 0x11: D[sp - 2] = (D[sp - 2] - D[sp - 1]) | 0; sp--; break;
      case 0x12: D[sp - 2] = Math.imul(D[sp - 2], D[sp - 1]); sp--; break;
      case 0x13: {
        const a = D[sp - 2], b = D[sp - 1];
        if (b === 0) { exit = 4; break; }
        D[sp - 2] = a === -2147483648 && b === -1 ? a : (a / b) | 0; sp--; break;
      }
      case 0x14: {
        const a = D[sp - 2], b = D[sp - 1];
        if (b === 0) { exit = 4; break; }
        D[sp - 2] = b === -1 ? 0 : (a % b) | 0; sp--; break;
      }
      case 0x15: {
        const a = D[sp - 2] >>> 0, b = D[sp - 1] >>> 0;
        if (b === 0) { exit = 4; break; }
        D[sp - 2] = Math.floor(a / b) | 0; sp--; break;
      }
      case 0x16: {
        const a = D[sp - 2] >>> 0, b = D[sp - 1] >>> 0;
        if (b === 0) { exit = 4; break; }
        D[sp - 2] = (a % b) | 0; sp--; break;
      }
      case 0x17: D[sp - 1] = (-D[sp - 1]) | 0; break;
      case 0x18: D[sp - 2] &= D[sp - 1]; sp--; break;
      case 0x19: D[sp - 2] |= D[sp - 1]; sp--; break;
      case 0x1a: D[sp - 2] ^= D[sp - 1]; sp--; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x1c: D[sp - 2] = D[sp - 2] << (D[sp - 1] & 31); sp--; break;
      case 0x1d: D[sp - 2] = D[sp - 2] >> (D[sp - 1] & 31); sp--; break;
      case 0x1e: D[sp - 2] = (D[sp - 2] >>> (D[sp - 1] & 31)) | 0; sp--; break;
      case 0x20: D[sp - 2] = D[sp - 2] === D[sp - 1] ? 1 : 0; sp--; break;
      case 0x21: D[sp - 2] = D[sp - 2] < D[sp - 1] ? 1 : 0; sp--; break;
      case 0x22: D[sp - 2] = (D[sp - 2] >>> 0) < (D[sp - 1] >>> 0) ? 1 : 0; sp--; break;
      case 0x30: pc = next + rel; break;
      case 0x31: if (D[--sp] === 0) pc = next + rel; break;
      case 0x32: if (D[--sp] !== 0) pc = next + rel; break;
      case 0x33:
        if (csp === CALLS) { exit = 7; break; }
        C[csp++] = next; pc = prog[next - 2] | (prog[next - 1] << 8); break;
      case 0x34:
        if (csp === 0) { exit = 8; break; }
        pc = C[--csp]; break;
      case 0x40: {
        const a = D[sp - 1];
        if (a < 0 || a >= MEM) { exit = 6; break; }
        D[sp - 1] = M[a]; break;
      }
      case 0x41: {
        const a = D[sp - 1];
        if (a < 0 || a >= MEM) { exit = 6; break; }
        M[a] = D[sp - 2]; sp -= 2; break;
      }
      case 0x50: {
        const s = String(D[sp - 1]);
        if (olen + s.length > OUTMAX) { exit = 11; break; }
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        sp--; break;
      }
      case 0x51:
        if (olen + 1 > OUTMAX) { exit = 11; break; }
        out[olen++] = D[sp - 1] & 255; sp--; break;
      case 0x52: D[sp++] = inPos < input.length ? input[inPos++] : -1; break;
      case 0x53: exit = D[sp - 1] & 255; sp--; break;
    }
  }
  return { out: out.subarray(0, olen), exit };
}

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

for (const id of readdirSync(IN_DIR).sort()) {
  let r: { out: Uint8Array; exit: number };
  try {
    const prog = new Uint8Array(readFileSync(join(IN_DIR, id, 'program.bin')));
    const f = join(IN_DIR, id, 'input.bin');
    r = run(prog, existsSync(f) ? new Uint8Array(readFileSync(f)) : new Uint8Array(0));
  } catch {
    r = { out: new Uint8Array(0), exit: 0 };
  }
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), r.out);
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), `${r.exit}\n`);
}
