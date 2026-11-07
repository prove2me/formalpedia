-- Prove2me | Definitions.Def_BFAlmostLinear_Machine
-- name    : BFAlmostLinear_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:37:53.386015+00:00
-- url     : https://prove2.me/theorems/9f1196cb-bbad-49ac-b7fc-23769db50354
-- title:
--   Word/real RAM with fair coins: programs, runs, word bound, coin tape
-- statement:
--   A **program** is a finite list of instructions together with a word exponent $c$. The machine has two register banks and two memories, all initialised to $0$ except the input cells.
--
--   1. **Integer bank** (registers and a memory addressed by integers): integer literals, $+$, $-$, $\times$, floor division $\lfloor a/b\rfloor$, shifts $a\cdot 2^b$ and $\lfloor a/2^b\rfloor$, bit length, load, store, and the jump "if $a\le b$ go to $\ell$".
--   2. **Real bank** (registers and a memory addressed by integers): the literal $0$, $+$, $-$, copy, load, store, and a three-way jump on $<$, $=$, $>$.
--   3. `coin d` writes the next bit of an infinite tape $\tau\in\{0,1\}^{\mathbb N}$ to an integer register.
--   4. `halt`.
--
--   There is no real literal other than $0$, no real multiplication, division or floor, and no conversion between the banks.
--
--   Every executed instruction costs one step. On input size parameter $B$ the **word bound** is $W=B^c$: an integer result, memory address or shift amount outside $[-W,W]$ sends the machine to a **stuck** state, which never halts; an invalid program counter is stuck as well. Halted and stuck states repeat forever, so the running time on a tape is the index of the first halted state. The tape law is the product of fair coins on $\{0,1\}^{\mathbb N}$.
--
--   This is the model in which "there is an algorithm" of Theorem 1.1 and of the algorithmic milestones is read.
--
--   **Formalization Note** The paper names no machine. The paper's algorithm only adds, subtracts and compares reals, and all its integer quantities are polynomial in the input size, so it fits this model, the weakest one that carries it. A real floor or real multiplication would let one cell encode many numbers and would empty a running-time bound.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), Theorem 1.1, p.1 (machine not named in the paper); §1.1, p.2

import Mathlib

namespace BFAlmostLinear

open MeasureTheory

/-!
# The word/real RAM with fair coins

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…). The paper names no machine for Theorem 1.1, p.1, "There is a (Las Vegas) randomized
algorithm … which runs in m^{1+o(1)} time"; §1.1, p.2 fixes "(possibly negative) real edge weights".

A program is a finite list of instructions over two banks, together with a word exponent `c`.

* **Integer bank.** Registers `ℕ → ℤ` and a memory `ℤ → ℤ`. Instructions: integer literal, `+`, `−`, `×`,
  floor division `⌊a/b⌋` (with `⌊a/0⌋ = 0`), shifts `a·2^b` and `⌊a/2^b⌋`, bit length, load, store, and
  the jump "if `a ≤ b` go to `target`".
* **Real bank.** Registers `ℕ → ℝ` and a memory `ℤ → ℝ` addressed by integers. Instructions: literal
  zero, `+`, `−`, copy, load, store, and the three-way jump on `<`, `=`, `>`.
* `coin d` writes the next fair bit of the tape to integer register `d`.
* `halt`.

**Formalization Note.**
* The paper only adds, subtracts and compares reals, and every integer quantity it uses is polynomial in
  the input size. There is no real literal other than `0`, no real multiplication, division or floor,
  and no cast between the banks. No constructor carries a function or a real number. This is the weakest
  model the paper's algorithm fits, so a theorem about it is the strongest reading of "algorithm".
* **Word bound.** `step` takes the word bound `W`; each theorem fixes `W` as a polynomial in its input
  size with the exponent `wordExp` chosen with the program. An integer result, a memory address or a
  shift amount outside `[−W, W]` sends the machine to a stuck state, which never halts.
* **Cost.** Every executed instruction, including `coin` and `halt`, is one step. A halted state and a
  stuck state stutter, so the running time is the index of the first halted state. An invalid program
  counter is stuck.
-/

namespace Machine

/-- An instruction. Register indices and jump targets are natural numbers. -/
inductive Instr : Type
  | iconst (d : ℕ) (k : ℤ)
  | iadd (d a b : ℕ)
  | isub (d a b : ℕ)
  | imul (d a b : ℕ)
  | idiv (d a b : ℕ)
  | ishl (d a b : ℕ)
  | ishr (d a b : ℕ)
  | ibitlen (d a : ℕ)
  | iload (d a : ℕ)
  | istore (a b : ℕ)
  | ijle (a b target : ℕ)
  | rzero (d : ℕ)
  | radd (d a b : ℕ)
  | rsub (d a b : ℕ)
  | rcopy (d a : ℕ)
  | rload (d a : ℕ)
  | rstore (a b : ℕ)
  | rcmp (a b tlt teq tgt : ℕ)
  | coin (d : ℕ)
  | halt
  deriving DecidableEq

/-- A program: a finite instruction list and the word exponent `c` of its word bound. -/
structure Program : Type where
  code : List Instr
  wordExp : ℕ

/-- `NoCoin P`: no `coin` instruction occurs in `P`, i.e. `P` is deterministic. -/
def NoCoin (P : Program) : Prop := ∀ d : ℕ, Instr.coin d ∉ P.code

/-- A machine state. `cursor` is the position of the next unread bit of the coin tape. -/
structure State : Type where
  pc : ℕ
  ireg : ℕ → ℤ
  imem : ℤ → ℤ
  rreg : ℕ → ℝ
  rmem : ℤ → ℝ
  cursor : ℕ
  halted : Bool
  stuck : Bool

/-- The word bound `W = B^c` of the program `P` on an input of size parameter `B`. -/
def wordBound (P : Program) (B : ℕ) : ℤ := (B : ℤ) ^ P.wordExp

/-- `z` fits in a word: `−W ≤ z ≤ W`. -/
def Fits (W z : ℤ) : Prop := -W ≤ z ∧ z ≤ W

instance (W z : ℤ) : Decidable (Fits W z) := by unfold Fits; infer_instance

/-- The stuck state reached from `σ`. -/
def State.toStuck (σ : State) : State := { σ with stuck := true }

/-- Write the integer `v` to register `d` and advance, or get stuck if `v` does not fit. -/
def setI (W : ℤ) (σ : State) (d : ℕ) (v : ℤ) : State :=
  if Fits W v then { σ with ireg := Function.update σ.ireg d v, pc := σ.pc + 1 } else σ.toStuck

/-- Write the real `v` to real register `d` and advance. -/
def setR (σ : State) (d : ℕ) (v : ℝ) : State :=
  { σ with rreg := Function.update σ.rreg d v, pc := σ.pc + 1 }

/-- Execute one instruction under word bound `W`, reading coins from the tape `τ`. -/
noncomputable def exec1 (W : ℤ) (τ : ℕ → Bool) (σ : State) : Instr → State
  | .iconst d k => setI W σ d k
  | .iadd d a b => setI W σ d (σ.ireg a + σ.ireg b)
  | .isub d a b => setI W σ d (σ.ireg a - σ.ireg b)
  | .imul d a b => setI W σ d (σ.ireg a * σ.ireg b)
  | .idiv d a b => setI W σ d (Int.fdiv (σ.ireg a) (σ.ireg b))
  | .ishl d a b =>
      if 0 ≤ σ.ireg b ∧ σ.ireg b ≤ W then setI W σ d (σ.ireg a * 2 ^ (σ.ireg b).toNat)
      else σ.toStuck
  | .ishr d a b =>
      if 0 ≤ σ.ireg b ∧ σ.ireg b ≤ W then setI W σ d (Int.fdiv (σ.ireg a) (2 ^ (σ.ireg b).toNat))
      else σ.toStuck
  | .ibitlen d a => setI W σ d (Nat.size (σ.ireg a).natAbs)
  | .iload d a => if Fits W (σ.ireg a) then setI W σ d (σ.imem (σ.ireg a)) else σ.toStuck
  | .istore a b =>
      if Fits W (σ.ireg a) then
        { σ with imem := Function.update σ.imem (σ.ireg a) (σ.ireg b), pc := σ.pc + 1 }
      else σ.toStuck
  | .ijle a b target =>
      if σ.ireg a ≤ σ.ireg b then { σ with pc := target } else { σ with pc := σ.pc + 1 }
  | .rzero d => setR σ d 0
  | .radd d a b => setR σ d (σ.rreg a + σ.rreg b)
  | .rsub d a b => setR σ d (σ.rreg a - σ.rreg b)
  | .rcopy d a => setR σ d (σ.rreg a)
  | .rload d a => if Fits W (σ.ireg a) then setR σ d (σ.rmem (σ.ireg a)) else σ.toStuck
  | .rstore a b =>
      if Fits W (σ.ireg a) then
        { σ with rmem := Function.update σ.rmem (σ.ireg a) (σ.rreg b), pc := σ.pc + 1 }
      else σ.toStuck
  | .rcmp a b tlt teq tgt =>
      { σ with pc := if σ.rreg a < σ.rreg b then tlt else if σ.rreg a = σ.rreg b then teq else tgt }
  | .coin d =>
      { σ with ireg := Function.update σ.ireg d (if τ σ.cursor then 1 else 0),
               pc := σ.pc + 1, cursor := σ.cursor + 1 }
  | .halt => { σ with halted := true }

/-- One step. Halted and stuck states stutter; an invalid program counter is stuck. -/
noncomputable def step (P : Program) (W : ℤ) (τ : ℕ → Bool) (σ : State) : State :=
  if σ.halted || σ.stuck then σ else
    match P.code[σ.pc]? with
    | none => σ.toStuck
    | some ins => exec1 W τ σ ins

/-- The initial state with the given memories: registers `0`, program counter `0`, tape cursor `0`. -/
def initState (imem : ℤ → ℤ) (rmem : ℤ → ℝ) : State where
  pc := 0
  ireg := fun _ => 0
  imem := imem
  rreg := fun _ => 0
  rmem := rmem
  cursor := 0
  halted := false
  stuck := false

/-- The state after `T` steps of `P` from `σ₀`, under word bound `W` and coin tape `τ`. -/
noncomputable def run (P : Program) (W : ℤ) (τ : ℕ → Bool) (σ₀ : State) (T : ℕ) : State :=
  (step P W τ)^[T] σ₀

/-- The all-`false` tape, used to run a program that has no `coin` instruction. -/
def zeroTape : ℕ → Bool := fun _ => false

/-- The law of the coin tape: i.i.d. fair bits. -/
noncomputable def coinTape : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure

/-- `P` has halted within `T` steps from `σ₀` on the tape `τ`. -/
def HaltsWithin (P : Program) (W : ℤ) (τ : ℕ → Bool) (σ₀ : State) (T : ℕ) : Prop :=
  (run P W τ σ₀ T).halted = true

end Machine

end BFAlmostLinear


