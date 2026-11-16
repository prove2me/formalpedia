-- Prove2me | Definitions.Def_DynStrings_Supplement_WordRAM
-- name    : DynStrings_Supplement_WordRAM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:50:36.633483+00:00
-- url     : https://prove2.me/theorems/33f3cbe1-4c8b-4559-a80a-393fbc82e974
-- title:
--   A randomized word RAM with $\mathrm{Uniform}(r)$ and allocated memory blocks (§6.2, App. A.1)
-- statement:
--   The model of computation of §6.2 and Appendix A.1. A **word** is a $w$-bit bit vector. A program is a finite list of instructions over registers $[i]$, and every executed instruction costs one step:
--
--   1. constants, register copies, $+,-,\cdot$ modulo $2^w$, unsigned division and remainder ($x/0=0$, $x\bmod 0=x$), bitwise and/or/xor, shifts, unsigned comparison, the index of the most significant set bit, equality tests and conditional jumps;
--   2. $[i]:=\mathrm{Uniform}([j])$, a uniformly random element of $[0\,.\,.\,[j])$ for a positive word $[j]$ ($[j]=0$ is a fault). The randomness is a coin sequence $\omega\in[0,1]^{\mathbb N}$ with the product uniform law, and the $c$-th draw with bound $r$ is $\min(\lfloor\omega_c r\rfloor,r-1)$. There is no other source of randomness;
--   3. allocation of a block of $[j]$ words, whose words are uninitialized (arbitrary words given by a function `junk`), freeing a block, and reading or writing word $o$ of a block through a pointer and an offset word. An access outside a live block is a fault.
--
--   Pointers are opaque: they occupy one word and can be stored, copied and compared, but not used in arithmetic, so addresses are unbounded and unobservable. Blocks marked as the caller's can be read but not written or freed. The **space** of a memory state is $\sum(\text{size}+1)$ over the live blocks of the data structure: the allocated words plus one word of overhead per block. A run halts at `halt` (or past the end of the program); a fault makes it stuck.
--
--   This machine gives the running time and the space of the data structure in Theorem 6.1.
--
--   **Formalization Note** `step` is one instruction, `run` iterates it, `Halts` says the run reaches `halted`, and `haltTime` is the least such number of steps. The program uses only the finitely many registers it names, so registers add $O(1)$ words.
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), §6.2, p.28 (PDF p.29) and p.29 (PDF p.30, Space); Appendix A.1, pp.58–59 (PDF pp.59–60)

import Mathlib

namespace DynStrings.Supplement

/-!
# A randomized word RAM with `Uniform(r)` and allocated memory blocks

Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript,
sha256 cfcb3de9…), §6.2, p.28 (model of computation) and p.29 (space), and Appendix A.1,
pp.58–59 (memory allocation).

**Formalization Note.**
* **Words.** A word is a `BitVec w`. Arithmetic (`+`, `−`, `·` modulo `2^w`, unsigned division and
  remainder with `x / 0 = 0`, `x % 0 = x`), bitwise `and`/`or`/`xor`, shifts, unsigned comparison,
  and the index of the most significant set bit (`Nat.log2`, `0` for the zero word) each cost one
  step. Equality test, register copy, a constant load and a conditional jump also cost one step.
* **Randomness.** `unif i j` is the paper's `Uniform(r)`: for a positive word `r = [j]` it writes a
  uniformly random element of `[0 . . r)`. The randomness is a coin sequence
  `ω : ℕ → [0, 1]`; the `c`-th executed `unif` with bound `r` returns `min ⌊ω_c · r⌋ (r − 1)`,
  which is uniform on `[0 . . r)` and independent of the other draws under `coinLaw`, the product of
  uniform laws on `[0, 1]`. `unif` with `r = 0` is a fault. There are no other random primitives (no
  random hash functions or oracles).
* **Memory (App. A.1).** Memory consists of allocated blocks. `alloc i j` allocates a block of `[j]`
  words in one step and puts a pointer to it in register `i`; its words are uninitialized: they hold
  the arbitrary words `junk b o` (block number `b`, offset `o`), and `junk` is universally quantified
  in every statement. `free i` frees a block in one step. Word `o` of a block is read or written in
  one step (`load`, `store`) through a pointer and an offset word; an access outside the block, or
  through a value that is not a pointer to a live block, is a fault. Pointers are opaque: they can be
  stored, copied and compared for equality, but not used in arithmetic, so the (unbounded) address
  of a block is not observable, matching "no bound is imposed on the largest address". A pointer
  occupies one word of space. Blocks are never moved, so a pointer is stable until its block is freed.
* **Caller blocks.** A block flagged `callerOwned` belongs to the caller (an input array). The
  program may read it but not write or free it.
* **Space.** The space of a memory state is `∑ (size + 1)` over the live blocks owned by the data
  structure: the total size of the allocated blocks plus an overhead of one word per block. Gaps and
  freed blocks are not counted. The program's registers are finitely many words (only the registers
  named in the program text are used).
* **Faults.** A faulting step moves the machine to the absorbing status `stuck`; `halt`, or fetching
  past the end of the program, moves it to `halted`. Every executed instruction is one step.
-/

/-- A register or memory word: a `w`-bit word, or an opaque pointer to the block with the given
number. -/
inductive Val (w : ℕ) where
  | word (x : BitVec w)
  | ptr (b : ℕ)
  deriving DecidableEq

/-- The binary word operations, each costing one step. -/
inductive BinOp where
  | add | sub | mul | udiv | umod | and | or | xor | shl | shr | ult

/-- The value of a binary word operation (`udiv`, `umod` unsigned with `x / 0 = 0`,
`x % 0 = x`; `ult` is `1` if `x < y` unsigned and `0` otherwise). -/
def BinOp.eval {w : ℕ} : BinOp → BitVec w → BitVec w → BitVec w
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .udiv, x, y => x / y
  | .umod, x, y => x % y
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y
  | .shl, x, y => x <<< y.toNat
  | .shr, x, y => x >>> y.toNat
  | .ult, x, y => if x.toNat < y.toNat then 1 else 0

/-- The instructions; `i j k` name registers, `l` is a position in the program. -/
inductive Instr where
  /-- `[i] := c mod 2^w` -/
  | const (i c : ℕ)
  /-- `[i] := [j]` -/
  | mov (i j : ℕ)
  /-- `[i] := [j] op [k]` on words -/
  | bin (op : BinOp) (i j k : ℕ)
  /-- `[i] :=` index of the most significant set bit of the word `[j]` (`0` for the zero word) -/
  | msb (i j : ℕ)
  /-- `[i] := 1` if `[j] = [k]` (as words or as pointers), else `0` -/
  | eq (i j k : ℕ)
  /-- if `[i]` is not the zero word, go to position `l` -/
  | bnz (i l : ℕ)
  /-- `[i] :=` word number `[k]` of the block `[j]` -/
  | load (i j k : ℕ)
  /-- word number `[j]` of the block `[i]` `:= [k]` -/
  | store (i j k : ℕ)
  /-- `[i] :=` a pointer to a newly allocated, uninitialized block of `[j]` words -/
  | alloc (i j : ℕ)
  /-- free the block `[i]` -/
  | free (i : ℕ)
  /-- `[i] := Uniform([j])`, a uniformly random element of `[0 . . [j])` -/
  | unif (i j : ℕ)
  /-- stop -/
  | halt

/-- A program is a finite list of instructions. -/
abbrev Program := List Instr

/-- An allocated block: its size in words, its contents, and whether it belongs to the caller. -/
structure Block (w : ℕ) where
  size : ℕ
  data : ℕ → Val w
  callerOwned : Bool

/-- A memory state: registers, the allocated blocks by number (block numbers are never reused),
the number of the next block, and the index of the next coin. -/
structure Mem (w : ℕ) where
  regs : ℕ → Val w
  heap : ℕ → Option (Block w)
  next : ℕ
  coin : ℕ

/-- The status of a running machine. -/
inductive Status where
  | running | halted | stuck
  deriving DecidableEq

/-- A configuration: program counter, memory, status. -/
structure Config (w : ℕ) where
  pc : ℕ
  mem : Mem w
  status : Status

/-- A coin sequence: one uniform number in `[0, 1]` per executed `unif`. -/
abbrev Coins := ℕ → unitInterval

/-- The law of the coins: independent uniform numbers in `[0, 1]`. -/
noncomputable def coinLaw : MeasureTheory.Measure Coins :=
  MeasureTheory.Measure.infinitePi fun _ => MeasureTheory.volume

/-- `Uniform(r)` from the coin `u`: `min ⌊u · r⌋ (r − 1)`, uniform on `[0 . . r)` for uniform `u`. -/
noncomputable def draw (u : unitInterval) (r : ℕ) : ℕ := min ⌊(u : ℝ) * r⌋₊ (r - 1)

/-- Write `v` into register `i`. -/
def Mem.setReg {w : ℕ} (m : Mem w) (i : ℕ) (v : Val w) : Mem w :=
  { m with regs := Function.update m.regs i v }

/-- One step of program `P` with uninitialized-memory contents `junk` and coins `ω`. Halted and
stuck configurations do not change. -/
noncomputable def step {w : ℕ} (junk : ℕ → ℕ → BitVec w) (P : Program) (ω : Coins)
    (c : Config w) : Config w :=
  if c.status ≠ .running then c else
  let m := c.mem
  let adv : Mem w → Config w := fun m' => ⟨c.pc + 1, m', .running⟩
  let stuck : Config w := ⟨c.pc, m, .stuck⟩
  match P[c.pc]? with
  | none => ⟨c.pc, m, .halted⟩
  | some .halt => ⟨c.pc, m, .halted⟩
  | some (.const i n) => adv (m.setReg i (.word (BitVec.ofNat w n)))
  | some (.mov i j) => adv (m.setReg i (m.regs j))
  | some (.bin op i j k) =>
    match m.regs j, m.regs k with
    | .word x, .word y => adv (m.setReg i (.word (op.eval x y)))
    | _, _ => stuck
  | some (.msb i j) =>
    match m.regs j with
    | .word x => adv (m.setReg i (.word (BitVec.ofNat w (Nat.log2 x.toNat))))
    | _ => stuck
  | some (.eq i j k) => adv (m.setReg i (.word (if m.regs j = m.regs k then 1 else 0)))
  | some (.bnz i l) => if m.regs i = .word 0 then adv m else ⟨l, m, .running⟩
  | some (.load i j k) =>
    match m.regs j, m.regs k with
    | .ptr b, .word x =>
      match m.heap b with
      | some B => if x.toNat < B.size then adv (m.setReg i (B.data x.toNat)) else stuck
      | none => stuck
    | _, _ => stuck
  | some (.store i j k) =>
    match m.regs i, m.regs j with
    | .ptr b, .word x =>
      match m.heap b with
      | some B =>
        if x.toNat < B.size ∧ B.callerOwned = false then
          adv { m with
            heap := Function.update m.heap b
              (some { B with data := Function.update B.data x.toNat (m.regs k) }) }
        else stuck
      | none => stuck
    | _, _ => stuck
  | some (.alloc i j) =>
    match m.regs j with
    | .word x =>
      adv ⟨Function.update m.regs i (.ptr m.next),
        Function.update m.heap m.next (some ⟨x.toNat, fun o => .word (junk m.next o), false⟩),
        m.next + 1, m.coin⟩
    | _ => stuck
  | some (.free i) =>
    match m.regs i with
    | .ptr b =>
      match m.heap b with
      | some B =>
        if B.callerOwned = false then adv { m with heap := Function.update m.heap b none }
        else stuck
      | none => stuck
    | _ => stuck
  | some (.unif i j) =>
    match m.regs j with
    | .word x =>
      if x.toNat = 0 then stuck
      else adv ⟨Function.update m.regs i (.word (BitVec.ofNat w (draw (ω m.coin) x.toNat))),
        m.heap, m.next, m.coin + 1⟩
    | _ => stuck

/-- The configuration after `k` steps. -/
noncomputable def run {w : ℕ} (junk : ℕ → ℕ → BitVec w) (P : Program) (ω : Coins)
    (c : Config w) (k : ℕ) : Config w :=
  (step junk P ω)^[k] c

/-- The run from `c` halts normally (reaches `halted`, never `stuck`). -/
def Halts {w : ℕ} (junk : ℕ → ℕ → BitVec w) (P : Program) (ω : Coins) (c : Config w) : Prop :=
  ∃ k, (run junk P ω c k).status = .halted

open Classical in
/-- The running time: the number of steps until the run halts (`0` if it does not halt; every use
is guarded by `Halts`). -/
noncomputable def haltTime {w : ℕ} (junk : ℕ → ℕ → BitVec w) (P : Program) (ω : Coins)
    (c : Config w) : ℕ :=
  if h : Halts junk P ω c then Nat.find h else 0

/-- The space of a memory state: `∑ (size + 1)` over the live blocks owned by the data structure. -/
def Mem.space {w : ℕ} (m : Mem w) : ℕ :=
  ∑ b ∈ Finset.range m.next,
    match m.heap b with
    | some B => if B.callerOwned then 0 else B.size + 1
    | none => 0

end DynStrings.Supplement


