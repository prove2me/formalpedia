-- Prove2me | Definitions.Def_ZlibCrc32_CrczModel
-- name    : ZlibCrc32_CrczModel
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T13:13:33.069796+00:00
-- url     : https://prove2.me/theorems/248872a7-4f6e-4d55-a6ec-3bd737eab2a7
-- title:
--   Model of zlib's braided crc32_z and an abstract AArch64 state, for intermediate results about crc32_z
-- statement:
--   Definitions over the placed library `zlibCrc32Lib` (bundle `ZlibCrc32_PlacedObj`) and the contracts bundle `ZlibCrc32_Spec`, used to state intermediate steps of a proof that the AArch64 code of zlib 1.3.1's `crc32_z` meets `crc32zSpec`.
--
--   **Bit-level model.** `T0 i` is word $i$ of `crc_table` and `TB k i` is word $256k + i$ of `crc_braid_table` (little-endian 32-bit words of the library's data bytes). `tstep c b` is one byte of the byte-wise loop, $T0[(c \oplus b) \bmod 256] \oplus (c \gg 8)$, and `crcBytes c bs` folds it over the bytes `bs`. `crcWord c w` is zlib's `crc_word(c ^ w)`: eight steps $x \mapsto T0[x \bmod 256] \oplus (x \gg 8)$ on the 64-bit value $c \oplus w$, low 32 bits. `wbytes w` lists the eight bytes of a 64-bit word, least significant first, and `wordLE bs i` is the little-endian 64-bit word of `bs[i], …, bs[i+7]` (missing bytes read as 0). `braidWord x` is $\bigoplus_{k<8} TB[k][\text{byte } k \text{ of } x]$. `braids bs p c k n` are the five braid CRCs after $k$ blocks of 40 bytes from offset $p$ (start: $c, 0, 0, 0, 0$; step: braid $n$ becomes `braidWord` of its value xor word $n$ of the block). `foldLast bs p c K` folds block $K$: starting from 0, `crcWord (v ^ braid n) (word n)` for $n = 0, …, 4$. `braidedResult crc bs q K` is $\lnot$ `crcBytes` of the rest of `bs` after the first $q + 40(K+1)$ bytes, started from `foldLast` with the braids started from `crcBytes (~crc)` of the first $q$ bytes.
--
--   **Machine.** `prog pl` is the placed program without hooks. `Regs` holds the 64-bit registers `x0..x28` and `x30`; `mkS s0 m sp pc ps r` is the state `s0` with memory `m`, stack pointer `sp`, program counter `pc`, flags `ps` and those registers replaced (`x29` and all other fields as in `s0`); `Regs.of s` reads them from a state. `FrameOk s0 m`: outside the 96 bytes below `s0.sp`, `m` has the same cells as `s0.mem`; inside, `m` is mapped read-write, not lazy-free, with the anonymous flag of `s0.mem`. `RoBytes m a bs`: the bytes `bs` are readable at `a` (value, read permission, not lazy-free). `RoOut s0 a bs`: `RoBytes` in `s0.mem` and outside the frame. `slot s0 j` is the address of the $j$-th 8-byte slot of the frame. `spIn s0` is `s0.sp - 96` (written as an addition). `Saved s0 m`: frame slots 0 and 2–11 hold `x30` and `x28, x27, …, x19` of `s0`. `RetOk s0 X sf`: `sf` is at the return address `x30` of `s0`, with the stack pointer of `s0`, running, the callee-saved registers of `s0`, `x0 = X`, and `FrameOk s0 sf.mem`. `Reach pl s0 X s`: some run of `prog pl` from `s` reaches a state with `RetOk s0 X`. `Env pl s0 bs m`: the library is placeable at `pl`, its code is loaded in `m`, `s0` is running with an aligned stack pointer, `FrameOk s0 m`, `Saved s0 m`, the buffer at `x1` of `s0` holds `bs` (readable in `m`, outside the frame), both tables are readable in `m` at their placed addresses and outside the frame, and `bs` has fewer than $2^{64}$ bytes.
-- source:
--   zlib 1.3.1 (J.-l. Gailly and M. Adler, January 22, 2024; https://zlib.net/fossils/zlib-1.3.1.tar.gz, SHA-256 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23), crc32.c lines 694–1013 (crc32_z, braided with N = 5, W = 8), as compiled for AArch64 (the placed library of the mission "zlib 1.3.1 CRC-32 on AArch64")

import Definitions.Def_ZlibCrc32_Spec

/-!
# A model of the braided `crc32_z` and an abstract machine state for proofs about it

Definitions used to state intermediate results of a proof that the AArch64 object code of
zlib 1.3.1's `crc32_z` (`zlibCrc32Lib`) meets `crc32zSpec`:

* a bit-level model of the computation: the byte-wise table step `tstep`, `crc_word` (`crcWord`),
  the braided step of N = 5 words of W = 8 bytes (`braidWord`, `braids`), the fold of the last
  block (`foldLast`) and the value returned along the braided path (`braidedResult`);
* an abstract machine state `mkS` (the entry state with memory, stack pointer, program counter,
  flags and the registers `x0..x28`, `x30` replaced), the judgment `Reach` (execution from a state
  returns to the caller with a given `x0`), the frame invariant `FrameOk`, readable bytes
  `RoBytes`, the saved registers `Saved` and the environment `Env` of a run.
-/

open Arm64 Arm64.Obj

namespace ZlibCrc32.Crcz

/-- Entry `i` of `crc_table`. -/
def T0 (i : ℕ) : BitVec 32 := word32 zlibCrc32PlacedData0 i

/-- Entry `i` of row `k` of `crc_braid_table`. -/
def TB (k i : ℕ) : BitVec 32 := word32 zlibCrc32PlacedData1 (256 * k + i)

/-- One byte of the byte-wise CRC: `crc = crc_table[(crc ^ b) & 0xff] ^ (crc >> 8)`. -/
def tstep (c : BitVec 32) (b : BitVec 8) : BitVec 32 :=
  T0 ((c ^^^ b.setWidth 32).toNat % 256) ^^^ (c >>> 8)

/-- The byte-wise CRC of `bs` from the register value `c`. -/
def crcBytes (c : BitVec 32) (bs : List (BitVec 8)) : BitVec 32 := bs.foldl tstep c

/-- One step of `crc_word` on a 64-bit word: `w = (w >> 8) ^ crc_table[w & 0xff]`. -/
def wstep (x : BitVec 64) : BitVec 64 := (T0 (x.toNat % 256)).setWidth 64 ^^^ (x >>> 8)

/-- `crc_word(crc ^ w)`: eight `wstep`s, low 32 bits. -/
def crcWord (c : BitVec 32) (w : BitVec 64) : BitVec 32 :=
  (wstep^[8] (c.setWidth 64 ^^^ w)).setWidth 32

/-- The eight bytes of a 64-bit word, least significant first. -/
def wbytes (w : BitVec 64) : List (BitVec 8) := (List.range 8).map fun j => w.extractLsb' (8 * j) 8

/-- The little-endian 64-bit word of the bytes `bs[i], …, bs[i+7]` (as `Memory.read64` builds it). -/
def wordLE (bs : List (BitVec 8)) (i : ℕ) : BitVec 64 :=
  bs.getD (i + 7) 0#8 ++ bs.getD (i + 6) 0#8 ++ bs.getD (i + 5) 0#8 ++ bs.getD (i + 4) 0#8 ++
    bs.getD (i + 3) 0#8 ++ bs.getD (i + 2) 0#8 ++ bs.getD (i + 1) 0#8 ++ bs.getD i 0#8

/-- The braided step of one 64-bit word `x = crc_n ^ word_n`:
`crc_braid_table[0][x & 0xff] ^ crc_braid_table[1][(x >> 8) & 0xff] ^ ⋯ ^ crc_braid_table[7][x >> 56]`. -/
def braidWord (x : BitVec 64) : BitVec 32 :=
  TB 0 (x.toNat % 256) ^^^ TB 1 ((x >>> 8).toNat % 256) ^^^ TB 2 ((x >>> 16).toNat % 256) ^^^
    TB 3 ((x >>> 24).toNat % 256) ^^^ TB 4 ((x >>> 32).toNat % 256) ^^^
    TB 5 ((x >>> 40).toNat % 256) ^^^ TB 6 ((x >>> 48).toNat % 256) ^^^ TB 7 ((x >>> 56).toNat % 256)

/-- The five braid CRCs after `k` blocks of 40 bytes of `bs` from offset `p`, starting from
`crc0 = c` and `crc1 = ⋯ = crc4 = 0`. -/
def braids (bs : List (BitVec 8)) (p : ℕ) (c : BitVec 32) : ℕ → ℕ → BitVec 32
  | 0, n => if n = 0 then c else 0
  | k + 1, n => braidWord ((braids bs p c k n).setWidth 64 ^^^ wordLE bs (p + 40 * k + 8 * n))

/-- The fold of the last block `K`: `crc = crc_word(crc0 ^ w0)`, then
`crc = crc_word(crc_n ^ w_n ^ crc)` for `n = 1, …, 4`. -/
def foldLast (bs : List (BitVec 8)) (p : ℕ) (c : BitVec 32) (K : ℕ) : BitVec 32 :=
  (List.range 5).foldl (fun v n => crcWord (v ^^^ braids bs p c K n) (wordLE bs (p + 40 * K + 8 * n))) 0

/-- The value `crc32_z` returns along the braided path: `q` prefix bytes byte-wise, `K + 1` blocks
braided (the last one folded), the rest byte-wise; post-conditioned. -/
def braidedResult (crc : BitVec 32) (bs : List (BitVec 8)) (q K : ℕ) : BitVec 32 :=
  ~~~ crcBytes (foldLast bs q (crcBytes (~~~ crc) (bs.take q)) K) (bs.drop (q + 40 * (K + 1)))

/-- The placed program the goal talks about. -/
def prog (pl : Placement) : Program := zlibCrc32Lib.program pl (fun _ => none) (fun _ => none)

/-- The general-purpose registers `crc32_z` may change. -/
structure Regs where
  x0 : BitVec 64
  x1 : BitVec 64
  x2 : BitVec 64
  x3 : BitVec 64
  x4 : BitVec 64
  x5 : BitVec 64
  x6 : BitVec 64
  x7 : BitVec 64
  x8 : BitVec 64
  x9 : BitVec 64
  x10 : BitVec 64
  x11 : BitVec 64
  x12 : BitVec 64
  x13 : BitVec 64
  x14 : BitVec 64
  x15 : BitVec 64
  x16 : BitVec 64
  x17 : BitVec 64
  x18 : BitVec 64
  x19 : BitVec 64
  x20 : BitVec 64
  x21 : BitVec 64
  x22 : BitVec 64
  x23 : BitVec 64
  x24 : BitVec 64
  x25 : BitVec 64
  x26 : BitVec 64
  x27 : BitVec 64
  x28 : BitVec 64
  x30 : BitVec 64

/-- Register `i` of `r`, defaulting to `d` for `x29` and `x31`. -/
def Regs.get (r : Regs) (d : BitVec 5 → BitVec 64) (i : BitVec 5) : BitVec 64 :=
  if i = 0#5 then r.x0 else
  if i = 1#5 then r.x1 else
  if i = 2#5 then r.x2 else
  if i = 3#5 then r.x3 else
  if i = 4#5 then r.x4 else
  if i = 5#5 then r.x5 else
  if i = 6#5 then r.x6 else
  if i = 7#5 then r.x7 else
  if i = 8#5 then r.x8 else
  if i = 9#5 then r.x9 else
  if i = 10#5 then r.x10 else
  if i = 11#5 then r.x11 else
  if i = 12#5 then r.x12 else
  if i = 13#5 then r.x13 else
  if i = 14#5 then r.x14 else
  if i = 15#5 then r.x15 else
  if i = 16#5 then r.x16 else
  if i = 17#5 then r.x17 else
  if i = 18#5 then r.x18 else
  if i = 19#5 then r.x19 else
  if i = 20#5 then r.x20 else
  if i = 21#5 then r.x21 else
  if i = 22#5 then r.x22 else
  if i = 23#5 then r.x23 else
  if i = 24#5 then r.x24 else
  if i = 25#5 then r.x25 else
  if i = 26#5 then r.x26 else
  if i = 27#5 then r.x27 else
  if i = 28#5 then r.x28 else
  if i = 30#5 then r.x30 else
  d i

/-- The abstract state. -/
def mkS (s0 : State) (m : Memory) (sp pc : BitVec 64) (ps : PState) (r : Regs) : State :=
  { s0 with regs := ⟨r.get s0.regs.regs⟩, mem := m, sp := sp, pc := pc, pstate := ps }

/-- The registers of a state. -/
def Regs.of (s : State) : Regs :=
  ⟨s.readReg64 (.gpr 0#5), s.readReg64 (.gpr 1#5), s.readReg64 (.gpr 2#5), s.readReg64 (.gpr 3#5), s.readReg64 (.gpr 4#5), s.readReg64 (.gpr 5#5), s.readReg64 (.gpr 6#5), s.readReg64 (.gpr 7#5), s.readReg64 (.gpr 8#5), s.readReg64 (.gpr 9#5), s.readReg64 (.gpr 10#5), s.readReg64 (.gpr 11#5), s.readReg64 (.gpr 12#5), s.readReg64 (.gpr 13#5), s.readReg64 (.gpr 14#5), s.readReg64 (.gpr 15#5), s.readReg64 (.gpr 16#5), s.readReg64 (.gpr 17#5), s.readReg64 (.gpr 18#5), s.readReg64 (.gpr 19#5), s.readReg64 (.gpr 20#5), s.readReg64 (.gpr 21#5), s.readReg64 (.gpr 22#5), s.readReg64 (.gpr 23#5), s.readReg64 (.gpr 24#5), s.readReg64 (.gpr 25#5), s.readReg64 (.gpr 26#5), s.readReg64 (.gpr 27#5), s.readReg64 (.gpr 28#5), s.readReg64 (.gpr 30#5)⟩

/-- The memory `m` agrees with the entry memory outside the 96-byte frame below the entry stack
pointer, and the frame stays mapped read-write and not lazy-free. -/
def FrameOk (s0 : State) (m : Memory) : Prop :=
  ∀ a, (¬ InRegion (s0.sp - 96#64) 96 a → m.cells a = s0.mem.cells a) ∧
    (InRegion (s0.sp - 96#64) 96 a → m.perm a = some Perm.rw ∧ m.isLazyFree a = false ∧
      m.isAnon a = s0.mem.isAnon a)

/-- Readable bytes `bs` at `a`. -/
def RoBytes (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)) : Prop :=
  ∀ i (hi : i < bs.length), m.read8 (a + BitVec.ofNat 64 i) = bs[i] ∧
    (m.perm (a + BitVec.ofNat 64 i)).r = true ∧ m.isLazyFree (a + BitVec.ofNat 64 i) = false

/-- Readable bytes `bs` at `a` in the entry memory, all outside the frame. -/
def RoOut (s0 : State) (a : BitVec 64) (bs : List (BitVec 8)) : Prop :=
  RoBytes s0.mem a bs ∧ ∀ i, i < bs.length → ¬ InRegion (s0.sp - 96#64) 96 (a + BitVec.ofNat 64 i)

/-- The `j`-th 8-byte slot of the frame (`j < 12`). -/
def slot (s0 : State) (j : ℕ) : BitVec 64 := s0.sp - 96#64 + BitVec.ofNat 64 (8 * j)

abbrev crcTabSym : String := "crc_table [zlib_crc32]"
abbrev braidTabSym : String := "crc_braid_table [zlib_crc32]"

/-- The values the subroutine must return with, given the entry state `s0`. -/
def RetOk (s0 : State) (X : BitVec 64) (sf : State) : Prop :=
  sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧ sf.status = .Running ∧
    CalleeSavedPreserved s0 sf ∧ sf.readReg64 (.gpr 0#5) = X ∧ FrameOk s0 sf.mem

/-- From `s`, the program reaches a return to the caller of `s0` with `x0 = X`. -/
def Reach (pl : Placement) (s0 : State) (X : BitVec 64) (s : State) : Prop :=
  ∃ sf, Steps (prog pl) s sf ∧ RetOk s0 X sf

/-- The stack pointer inside `crc32_z`'s frame. -/
abbrev spIn (s0 : State) : BitVec 64 := s0.sp + 18446744073709551520#64

/-- The callee-saved registers and the link register, saved in the frame. -/
def Saved (s0 : State) (m : Memory) : Prop :=
  m.read64 (slot s0 0) = s0.readReg64 (.gpr 30#5) ∧
  m.read64 (slot s0 2) = s0.readReg64 (.gpr 28#5) ∧ m.read64 (slot s0 3) = s0.readReg64 (.gpr 27#5) ∧
  m.read64 (slot s0 4) = s0.readReg64 (.gpr 26#5) ∧ m.read64 (slot s0 5) = s0.readReg64 (.gpr 25#5) ∧
  m.read64 (slot s0 6) = s0.readReg64 (.gpr 24#5) ∧ m.read64 (slot s0 7) = s0.readReg64 (.gpr 23#5) ∧
  m.read64 (slot s0 8) = s0.readReg64 (.gpr 22#5) ∧ m.read64 (slot s0 9) = s0.readReg64 (.gpr 21#5) ∧
  m.read64 (slot s0 10) = s0.readReg64 (.gpr 20#5) ∧ m.read64 (slot s0 11) = s0.readReg64 (.gpr 19#5)

/-- What every block after the prologue knows: placement, code, frame, buffer and tables in the
current memory `m`. -/
structure Env (pl : Placement) (s0 : State) (bs : List (BitVec 8)) (m : Memory) : Prop where
  hP : zlibCrc32Lib.Placeable pl
  hCL : (prog pl).CodeLoaded m
  hrun : s0.status = .Running
  hal : s0.spAligned = true
  hF : FrameOk s0 m
  hS : Saved s0 m
  hbuf : RoBytes m (s0.readReg64 (.gpr 1#5)) bs
  hT : RoBytes m (pl.ρ crcTabSym) zlibCrc32PlacedData0
  hU : RoBytes m (pl.ρ braidTabSym) zlibCrc32PlacedData1
  hlen : bs.length < 2 ^ 64
  hbufO : ∀ i, i < bs.length →
    ¬ InRegion (s0.sp - 96#64) 96 (s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 i)
  hTO : ∀ i, i < zlibCrc32PlacedData0.length →
    ¬ InRegion (s0.sp - 96#64) 96 (pl.ρ crcTabSym + BitVec.ofNat 64 i)
  hUO : ∀ i, i < zlibCrc32PlacedData1.length →
    ¬ InRegion (s0.sp - 96#64) 96 (pl.ρ braidTabSym + BitVec.ofNat 64 i)

end ZlibCrc32.Crcz


