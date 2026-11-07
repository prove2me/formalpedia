-- Prove2me | Definitions.Def_DynBrooks_Machine
-- name    : DynBrooks_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:04:53.538696+00:00
-- url     : https://prove2.me/theorems/e06edc25-f904-4699-a1eb-a431f7e284dc
-- title:
--   §3 — the word-RAM with unit-cost random words and reads that block
-- statement:
--   The paper works "in the word-RAM model with $O(\log n)$-bit words and unit-cost access to independent random words" (§3). This definition fixes such a machine.
--
--   A **program** is a finite list of instructions, fixed before the word size $w$. A **configuration** consists of a program counter, a memory $\mathbb N\to\{0,1\}^w$ (all cells zero at the start), the list of input words not yet read, a **coin cursor**, the list of words written so far, and the set of memory cells written so far. The instructions are: $[i]:=1$; addition, subtraction, multiplication, unsigned division and remainder, bitwise and/or/xor, left and right shifts (all modulo $2^w$); indirect load and store; an unconditional jump and a jump on a negative word; $\mathtt{coin}\ i$, which stores the next word of the coin tape and advances the cursor; $\mathtt{read}\ i$, which stores the next pending input word and **blocks** (the machine does not move) if no input is pending; $\mathtt{write}\ i$; and $\mathtt{halt}$. Every executed instruction is one step.
--
--   The coin tape is a sequence $\omega=(\omega_0,\omega_1,\dots)$ of words, distributed as independent uniform words (the infinite product of the uniform law on $\{0,1\}^w$). A **completed state** is a configuration blocked at a $\mathtt{read}$ with no input pending. For a configuration $c$, $\mathrm{time}(c)\in\mathbb N\cup\{\infty\}$ is the number of steps until the first completed state, and $\infty$ if none is reached.
--
--   The machine reads an operation only by executing $\mathtt{read}$, so it cannot look ahead, and a configuration has seen exactly the coins below its cursor; this is what makes "fresh randomness" after a completed state meaningful.
--
--   **Formalization Note** The paper does not list instructions; this is a standard word-RAM instruction set. Division by zero follows the `BitVec` conventions ($x/0=0$, $x \bmod 0=x$).
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), §3, p.13 (PDF 15)

import Mathlib

namespace DynBrooks

open MeasureTheory

/-! # The word-RAM with coins and reads that block

Mishra, Mukherjee, *Fully Dynamic Brooks Coloring* (STOC 2027 submission, sha256 6542a9f1…), §3,
p.13 (PDF 15): "We work in the word-RAM model with O(log n)-bit words and unit-cost access to
independent random words."

**Formalization Note.** The paper names the model and not an instruction set. A program is a finite
list of instructions, fixed before the word size. A machine of word size `w` has memory
`ℕ → BitVec w` (all zero initially), a program counter, the pending input words, a coin cursor, the
words written so far, and the set of cells written so far (for space). Arithmetic is modulo `2^w`,
with `udiv x 0 = 0` and `umod x 0 = x` (the `BitVec` conventions). Comparisons are `sub` with `bltz`.
`coin i` stores the next word of the coin tape `ω : ℕ → BitVec w` and advances the cursor, so a
configuration has seen exactly the coins below its cursor. `read i` stores the next pending input
word and **blocks** when none is pending: the machine stays put until an operation is delivered, so
it cannot look ahead. Every executed instruction is one step. -/

/-- The instruction set. `[i]` denotes memory cell `i`. -/
inductive Instr where
  /-- `[i] := 1` -/
  | one (i : ℕ)
  /-- `[i] := [j] + [k]` -/
  | add (i j k : ℕ)
  /-- `[i] := [j] - [k]` -/
  | sub (i j k : ℕ)
  /-- `[i] := [j] * [k]` -/
  | mul (i j k : ℕ)
  /-- `[i] := [j] / [k]` (unsigned) -/
  | udiv (i j k : ℕ)
  /-- `[i] := [j] mod [k]` (unsigned) -/
  | umod (i j k : ℕ)
  /-- bitwise and -/
  | band (i j k : ℕ)
  /-- bitwise or -/
  | bor (i j k : ℕ)
  /-- bitwise xor -/
  | bxor (i j k : ℕ)
  /-- `[i] := [j] <<< [k]` -/
  | shl (i j k : ℕ)
  /-- `[i] := [j] >>> [k]` (logical) -/
  | shr (i j k : ℕ)
  /-- `[i] := [[j]]` -/
  | load (i j : ℕ)
  /-- `[[i]] := [j]` -/
  | store (i j : ℕ)
  /-- jump to `l` if `[i] < 0` as a signed word -/
  | bltz (i l : ℕ)
  /-- jump to `l` -/
  | jmp (l : ℕ)
  /-- `[i] :=` the next word of the coin tape -/
  | coin (i : ℕ)
  /-- `[i] :=` the next pending input word; blocks if none is pending -/
  | read (i : ℕ)
  /-- append `[i]` to the output -/
  | write (i : ℕ)
  | halt
  deriving DecidableEq

/-- A program is a finite list of instructions; execution starts at index `0`. -/
abbrev Program := List Instr

/-- A configuration of the machine with word size `w`. `coinPos` is the position of the next unused
coin, `written` the set of memory cells written so far. -/
structure Config (w : ℕ) where
  pc : ℕ
  mem : ℕ → BitVec w
  input : List ℕ
  coinPos : ℕ
  output : List ℕ
  written : Finset ℕ

namespace Config

variable {w : ℕ}

/-- Write `v` into cell `a` and advance the program counter. -/
def assign (c : Config w) (a : ℕ) (v : BitVec w) : Config w :=
  { c with pc := c.pc + 1, mem := Function.update c.mem a v, written := insert a c.written }

end Config

/-- One step on coin tape `ω`. A configuration at `halt`, outside the program, or at a `read` with no
pending input is left unchanged. -/
def step {w : ℕ} (P : Program) (ω : ℕ → BitVec w) (c : Config w) : Config w :=
  match P[c.pc]? with
  | none => c
  | some Instr.halt => c
  | some (Instr.one i) => c.assign i 1
  | some (Instr.add i j k) => c.assign i (c.mem j + c.mem k)
  | some (Instr.sub i j k) => c.assign i (c.mem j - c.mem k)
  | some (Instr.mul i j k) => c.assign i (c.mem j * c.mem k)
  | some (Instr.udiv i j k) => c.assign i (BitVec.udiv (c.mem j) (c.mem k))
  | some (Instr.umod i j k) => c.assign i (BitVec.umod (c.mem j) (c.mem k))
  | some (Instr.band i j k) => c.assign i (c.mem j &&& c.mem k)
  | some (Instr.bor i j k) => c.assign i (c.mem j ||| c.mem k)
  | some (Instr.bxor i j k) => c.assign i (c.mem j ^^^ c.mem k)
  | some (Instr.shl i j k) => c.assign i (c.mem j <<< (c.mem k).toNat)
  | some (Instr.shr i j k) => c.assign i (c.mem j >>> (c.mem k).toNat)
  | some (Instr.load i j) => c.assign i (c.mem (c.mem j).toNat)
  | some (Instr.store i j) => c.assign (c.mem i).toNat (c.mem j)
  | some (Instr.bltz i l) =>
      if (c.mem i).msb then { c with pc := l } else { c with pc := c.pc + 1 }
  | some (Instr.jmp l) => { c with pc := l }
  | some (Instr.coin i) => { c.assign i (ω c.coinPos) with coinPos := c.coinPos + 1 }
  | some (Instr.read i) =>
      match c.input with
      | [] => c
      | x :: rest => { c.assign i (BitVec.ofNat w x) with input := rest }
  | some (Instr.write i) => { c with pc := c.pc + 1, output := c.output ++ [(c.mem i).toNat] }

/-- The configuration after `t` steps from `c` on tape `ω`. -/
def run {w : ℕ} (P : Program) (ω : ℕ → BitVec w) (c : Config w) (t : ℕ) : Config w :=
  (step P ω)^[t] c

/-- A **completed state**: the machine is blocked at a `read` with no input pending. -/
def IsCompleted {w : ℕ} (P : Program) (c : Config w) : Prop :=
  (∃ i, P[c.pc]? = some (Instr.read i)) ∧ c.input = []

/-- The number of steps from `c` to the first completed state on tape `ω`, and `⊤` if no completed
state is ever reached (for instance after a `halt`). The infimum over the empty set in `ℕ∞` is `⊤`,
so a run that never completes exceeds every bound. -/
noncomputable def time {w : ℕ} (P : Program) (ω : ℕ → BitVec w) (c : Config w) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : IsCompleted P (run P ω c t)), (t : ℕ∞)

open Classical in
/-- The first completed state reached from `c` on tape `ω`, if there is one. -/
noncomputable def complete {w : ℕ} (P : Program) (ω : ℕ → BitVec w) (c : Config w) :
    Option (Config w) :=
  if h : ∃ t, IsCompleted P (run P ω c t) then some (run P ω c (Nat.find h)) else none

/-- Deliver the words of one operation to a completed state. -/
def feed {w : ℕ} (c : Config w) (inp : List ℕ) : Config w :=
  { c with input := inp }

/-- The discrete σ-algebra on words. -/
instance (w : ℕ) : MeasurableSpace (BitVec w) := ⊤

/-- The law of the coin tape: independent uniform words (`Measure.infinitePi` of the uniform law on
`BitVec w`). -/
noncomputable def coinMeasure (w : ℕ) : Measure (ℕ → BitVec w) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype (BitVec w)).toMeasure

end DynBrooks


