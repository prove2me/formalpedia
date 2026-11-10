-- Prove2me | Definitions.Def_IncrOpenAddr_NoTradeoff_Machine
-- name    : IncrOpenAddr_NoTradeoff_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:34:42.595336+00:00
-- url     : https://prove2.me/theorems/c5db24c8-54cd-4b5d-8cac-0d678e691e2b
-- title:
--   The word RAM with a hash oracle, an n-slot array and a read-only element counter
-- statement:
--   A **word RAM** with word size $w$: every word is a $w$-bit string (`BitVec w`), and arithmetic is modulo $2^w$. A **program** is a finite list of instructions, started at index $0$; immediates are natural numbers read modulo $2^w$, so one program runs at every word size. The machine has a private **scratch memory** (cells $0,1,2,\dots$, each a word), a **slot array** $A:\{0,\dots,n-1\}\to\{\text{empty}\}\cup\{\text{words}\}$ in which every slot is empty or holds exactly one key and nothing else, an **element counter** $c\in\mathbb N$, and a **hash oracle** $f:\mathrm{Word}_w\times\mathrm{Word}_w\to\mathrm{Word}_w$.
--
--   Instructions: copy; $+,-,\times$ modulo $2^w$; unsigned division and remainder ($x/0=0$, $x \bmod 0=x$); AND, OR, XOR, NOT; left and right shifts; **population count**; **highest set bit** ($\lfloor\log_2 x\rfloor$, and $0$ at $x=0$); unsigned comparison branches and jumps; direct and indirect scratch addressing; `hash d x y`: $d\leftarrow f(x,y)$; `slotRead`: read slot $i \bmod n$ (an occupied flag and the key); `slotWrite`: empty slot $i \bmod n$ or store a key in it (allowed only when the run may write); `count`: read the counter $c$; `halt`.
--
--   Every executed instruction is one **step**. A run that reaches an instruction it cannot execute (a `slotWrite` in a read-only run, a jump outside the program, $n=0$) is stuck and never halts. `haltTime` is the number of steps until the run halts ($\top$ if never), and `finalState` the state at halting. The state records the list of slots read so far, in order.
--
--   **Formalization Note.** Words are `BitVec w`; the array is `Fin n → Option (Word w)`, so a slot cannot carry extra bits. The counter is a parameter of the run, never stored in writable memory.
-- source:
--   Farach-Colton, Krapivin, Kuszmaul, Incremental Open Addressing Has No Time-Space Tradeoff, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 33 (PDF 34), Appendix A (Computational model); p. 1 (PDF 2), §1 clause 1

import Mathlib

set_option autoImplicit false

/-!
# The word RAM with a hash oracle, an `n`-slot array and an element counter

Farach-Colton, Krapivin, Kuszmaul, *Incremental Open Addressing Has No Time-Space Tradeoff*,
arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 33 (PDF 34), Appendix A, "Computational
model": "We use words of Θ(log n) bits, with unit-cost integer arithmetic (including
multiplication and division), bitwise operations, shifts, population count, and the
highest-set-bit operation. … Hash evaluations and priority threshold comparisons are assumed to
take constant time."  Open addressing, p. 1 (PDF 2), clause 1: an array of `n` slots, each storing
at most one element, plus O(1) words of metadata such as a counter of the elements present.

A program is a finite list of instructions over `w`-bit words; one program runs at every word
size (immediates are read modulo `2^w`).  Its private scratch memory is `ℕ → BitVec w`.  Besides
the scratch memory it can touch only
* the hash oracle `f : Word w → Word w → Word w` (instruction `hash`),
* the slot array `Fin n → Option (Word w)` (instructions `slotRead`, `slotWrite`), and
* the element counter `c` (instruction `count`, read-only).
Every executed instruction costs one step.
-/

namespace IncrOpenAddr.NoTradeoff

/-- A `w`-bit machine word. -/
abbrev Word (w : ℕ) := BitVec w

/-- Private scratch memory: cells `0, 1, 2, …` each holding a word. -/
abbrev Scratch (w : ℕ) := ℕ → Word w

/-- The slot array: `n` slots, each empty (`none`) or holding exactly one key (`some x`). -/
abbrev SlotArray (n w : ℕ) := Fin n → Option (Word w)

/-- A hash function: two words to one word (the fully random oracle). -/
abbrev HashFn (w : ℕ) := Word w → Word w → Word w

/-- An operand: an immediate natural number (read modulo `2^w`), a scratch cell, or the scratch
cell whose address is stored in a scratch cell. -/
inductive Operand where
  | imm (v : ℕ)
  | dir (a : ℕ)
  | ind (a : ℕ)
  deriving DecidableEq, Repr

/-- A destination: a scratch cell, direct or indirect. -/
inductive Dest where
  | dir (a : ℕ)
  | ind (a : ℕ)
  deriving DecidableEq, Repr

/-- Binary operations: arithmetic modulo `2^w`, unsigned division and remainder
(`x / 0 = 0`, `x % 0 = x`), bitwise AND/OR/XOR, shifts by the unsigned value of the second
operand. -/
inductive BinOp where
  | add | sub | mul | udiv | umod | band | bor | bxor | shl | shr
  deriving DecidableEq, Repr

/-- Unary operations: bitwise NOT, population count, highest set bit (`0` at `0`). -/
inductive UnOp where
  | bnot | popcount | msb
  deriving DecidableEq, Repr

/-- Unsigned comparisons for conditional branches. -/
inductive Cmp where
  | eq | ne | lt | le
  deriving DecidableEq, Repr

/-- The instruction set. -/
inductive Instr where
  /-- `d ← s` -/
  | copy (d : Dest) (s : Operand)
  /-- `d ← x op y` -/
  | bin (op : BinOp) (d : Dest) (x y : Operand)
  /-- `d ← op x` -/
  | un (op : UnOp) (d : Dest) (x : Operand)
  /-- `pc ← t` -/
  | jump (t : ℕ)
  /-- `if x cmp y then pc ← t` -/
  | branch (c : Cmp) (x y : Operand) (t : ℕ)
  /-- `d ← f(x, y)`: one evaluation of the hash oracle -/
  | hash (d : Dest) (x y : Operand)
  /-- read slot `i mod n`: `dFlag ← 1` and `dKey ← key` if it holds a key, else
  `dFlag ← 0`, `dKey ← 0` -/
  | slotRead (dFlag dKey : Dest) (i : Operand)
  /-- write slot `i mod n`: empty it if `flag = 0`, else store the key `key` (insertions only) -/
  | slotWrite (i flag key : Operand)
  /-- `d ← c`, the element counter (read-only) -/
  | count (d : Dest)
  | halt
  deriving DecidableEq, Repr

/-- A program: a finite list of instructions, started at index `0`. -/
abbrev Program := List Instr

variable {n w : ℕ}

/-- The value of an operand. -/
def Operand.read (mem : Scratch w) : Operand → Word w
  | .imm v => BitVec.ofNat w v
  | .dir a => mem a
  | .ind a => mem (mem a).toNat

/-- The scratch address a destination denotes. -/
def Dest.addr (mem : Scratch w) : Dest → ℕ
  | .dir a => a
  | .ind a => (mem a).toNat

/-- Store a word into a scratch cell. -/
def Scratch.write (mem : Scratch w) (a : ℕ) (v : Word w) : Scratch w :=
  fun b => if b = a then v else mem b

/-- Population count: the number of one bits. -/
def popcountW (x : Word w) : Word w :=
  BitVec.ofNat w ((List.range w).countP (fun i => x.getLsbD i))

/-- Highest set bit: `⌊log₂ x⌋`, and `0` at `x = 0`. -/
def msbW (x : Word w) : Word w := BitVec.ofNat w (Nat.log2 x.toNat)

def BinOp.eval : BinOp → Word w → Word w → Word w
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .udiv, x, y => x / y
  | .umod, x, y => x % y
  | .band, x, y => x &&& y
  | .bor, x, y => x ||| y
  | .bxor, x, y => x ^^^ y
  | .shl, x, y => x <<< y.toNat
  | .shr, x, y => x >>> y.toNat

def UnOp.eval : UnOp → Word w → Word w
  | .bnot, x => ~~~x
  | .popcount, x => popcountW x
  | .msb, x => msbW x

def Cmp.test : Cmp → Word w → Word w → Bool
  | .eq, x, y => decide (x = y)
  | .ne, x, y => decide (x ≠ y)
  | .lt, x, y => decide (x.toNat < y.toNat)
  | .le, x, y => decide (x.toNat ≤ y.toNat)

/-- A machine state: scratch memory, slot array, program counter, halting flag, and the list of
slots read so far, in order. -/
structure State (n w : ℕ) where
  mem : Scratch w
  arr : SlotArray n w
  pc : ℕ
  halted : Bool
  reads : List (Fin n)

/-- Execute one instruction.  `canWrite` is `false` for queries: a `slotWrite` is then stuck.
`f` is the hash oracle and `c` the element counter.  `none` means stuck. -/
def exec (canWrite : Bool) (f : HashFn w) (c : ℕ) (i : Instr) (s : State n w) :
    Option (State n w) :=
  let s' : State n w := { s with pc := s.pc + 1 }
  match i with
  | .copy d x => some { s' with mem := s.mem.write (d.addr s.mem) (x.read s.mem) }
  | .bin op d x y =>
      some { s' with mem := s.mem.write (d.addr s.mem) (op.eval (x.read s.mem) (y.read s.mem)) }
  | .un op d x => some { s' with mem := s.mem.write (d.addr s.mem) (op.eval (x.read s.mem)) }
  | .jump t => some { s' with pc := t }
  | .branch cmp x y t =>
      some { s' with pc := if cmp.test (x.read s.mem) (y.read s.mem) then t else s.pc + 1 }
  | .hash d x y => some { s' with mem := s.mem.write (d.addr s.mem) (f (x.read s.mem) (y.read s.mem)) }
  | .slotRead dF dK x =>
      if h : 0 < n then
        let j : Fin n := ⟨(x.read s.mem).toNat % n, Nat.mod_lt _ h⟩
        let m1 := s.mem.write (dF.addr s.mem) (if (s.arr j).isSome then 1 else 0)
        let m2 := m1.write (dK.addr m1) ((s.arr j).getD 0)
        some { s' with mem := m2, reads := s.reads ++ [j] }
      else none
  | .slotWrite x fl k =>
      if h : 0 < n ∧ canWrite = true then
        let j : Fin n := ⟨(x.read s.mem).toNat % n, Nat.mod_lt _ h.1⟩
        let v : Option (Word w) := if fl.read s.mem = 0 then none else some (k.read s.mem)
        some { s' with arr := Function.update s.arr j v }
      else none
  | .count d => some { s' with mem := s.mem.write (d.addr s.mem) (BitVec.ofNat w c) }
  | .halt => some { s' with halted := true }

/-- One step of program `P`; `none` if halted or stuck (including a `pc` outside `P`). -/
def step (canWrite : Bool) (f : HashFn w) (c : ℕ) (P : Program) (s : State n w) :
    Option (State n w) :=
  if s.halted then none
  else match P[s.pc]? with
    | none => none
    | some i => exec canWrite f c i s

/-- Run for at most `t` steps; a halted or stuck state stays put. -/
def runN (canWrite : Bool) (f : HashFn w) (c : ℕ) (P : Program) : ℕ → State n w → State n w
  | 0, s => s
  | t + 1, s => match step canWrite f c P s with
    | none => s
    | some s' => runN canWrite f c P t s'

/-- The number of steps until the run halts (`⊤` if it never halts). -/
noncomputable def haltTime (canWrite : Bool) (f : HashFn w) (c : ℕ) (P : Program)
    (s : State n w) : ℕ∞ := by
  classical
  exact if h : ∃ t, (runN canWrite f c P t s).halted = true then (Nat.find h : ℕ∞) else ⊤

/-- The state at halting, if the run halts. -/
noncomputable def finalState (canWrite : Bool) (f : HashFn w) (c : ℕ) (P : Program)
    (s : State n w) : Option (State n w) := by
  classical
  exact if h : ∃ t, (runN canWrite f c P t s).halted = true then
    some (runN canWrite f c P (Nat.find h) s) else none

end IncrOpenAddr.NoTradeoff


