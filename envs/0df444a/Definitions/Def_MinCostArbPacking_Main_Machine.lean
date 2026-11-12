-- Prove2me | Definitions.Def_MinCostArbPacking_Main_Machine
-- name    : MinCostArbPacking_Main_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:40:12.353866+00:00
-- url     : https://prove2.me/theorems/84bf9697-b96b-47a6-9cdf-b0b9bee469d4
-- title:
--   The deterministic unit-cost real RAM of §3.1
-- statement:
--   A **program** is a finite list of instructions over an integer bank (registers and a memory indexed by integers) and a real bank (registers and a memory indexed by integers).
--
--   1. Integer instructions: literal, $+$, $-$, $\times$, integer division by a nonzero divisor, indirect load and store, the jump "if $a\le b$", an unconditional jump.
--   2. Real instructions: the literal $0$, exact $+,-,\times,\div$ (nonzero divisor), copy, indirect load and store (addresses are integers), and jumps on $<$ and on $=$.
--   3. `halt`.
--
--   There is no floor, no conversion between the banks and no real-indexed addressing: integers see reals only through comparison outcomes. A run has a **word bound** $W$: an integer result or address outside $[-W,W]$, a division by zero or an invalid program counter makes the machine stuck forever. Every executed instruction costs one step. Inputs are written into memory cells $0,1,\dots$, outputs read from cells $-1,-2,\dots$.
--
--   This is the model behind "exact arithmetic operations and comparisons take constant time" (§3.1); because the bound of Theorem 1.1 does not depend on the costs and reals admit only exact arithmetic and comparisons, the algorithm is strongly polynomial.
--
--   **Formalization Note** Theorems quantify over every word bound $W\ge(\mathrm{size}+2)^c$ with $c$ fixed with the program, i.e. $\Theta(\log \mathrm{size})$-bit words, so unbounded-integer multiplication cannot be used for bit-parallel work. The step count is the number of iterations of the interpreter.
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §3.1, p.7

import Mathlib

set_option autoImplicit false

/-!
# The deterministic unit-cost real RAM

Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §3.1, p.7: "Exact arithmetic operations
and comparisons take constant time."

A program is a finite list of instructions over two banks.

* **Integer bank.** Registers `ℕ → ℤ` and an indirectly addressed memory `ℤ → ℤ`. Instructions:
  integer literal, `+`, `−`, `×`, integer (Lean `Int`, Euclidean) division by a nonzero divisor, load, store, the
  conditional jump "if `a ≤ b` go to `target`", and an unconditional jump.
* **Real bank.** Registers `ℕ → ℝ` and a memory `ℤ → ℝ` addressed by integers. Instructions: the
  literal `0`, exact `+`, `−`, `×`, `÷` (by a nonzero divisor), copy, load, store, and the
  conditional jumps on `<` and on `=`.
* `halt`.

There is no floor or other real-to-integer conversion, no integer-to-real conversion, and no
real-indexed addressing: the integer bank sees a real value only through the outcome of a real
comparison. No instruction carries a function or a real number other than `0`.

**Word size.** A run is parametrized by a word bound `W`. An integer literal, an integer result or
a memory address outside `[-W, W]`, a division by zero (in either bank) or a program counter outside
the program sends the machine to a stuck state, which never halts. Theorems quantify over every
`W ≥ (size + 2)^c` with `c` fixed together with the program, i.e. `Θ(log size)`-bit words.

**Cost.** Every executed instruction, including `halt`, costs one step; the step count is the
number of iterations of `step`. A halted state stutters.
-/

namespace MinCostArbPacking.Main

namespace Machine

/-- An instruction. Register indices and jump targets are natural numbers. -/
inductive Instr : Type
  | iconst (d : ℕ) (z : ℤ)
  | iadd (d a b : ℕ)
  | isub (d a b : ℕ)
  | imul (d a b : ℕ)
  | idiv (d a b : ℕ)
  | iload (d a : ℕ)
  | istore (a b : ℕ)
  | ijle (a b target : ℕ)
  | jmp (target : ℕ)
  | rzero (d : ℕ)
  | radd (d a b : ℕ)
  | rsub (d a b : ℕ)
  | rmul (d a b : ℕ)
  | rdiv (d a b : ℕ)
  | rcopy (d a : ℕ)
  | rload (d a : ℕ)
  | rstore (a b : ℕ)
  | rjlt (a b target : ℕ)
  | rjeq (a b target : ℕ)
  | halt
  deriving DecidableEq

/-- A program: a finite instruction list. -/
abbrev Program : Type := List Instr

/-- A machine state. -/
structure State : Type where
  pc : ℕ
  ireg : ℕ → ℤ
  imem : ℤ → ℤ
  rreg : ℕ → ℝ
  rmem : ℤ → ℝ
  halted : Bool
  stuck : Bool

/-- `z` fits in a word. -/
def Fits (W z : ℤ) : Prop := -W ≤ z ∧ z ≤ W

instance (W z : ℤ) : Decidable (Fits W z) := by unfold Fits; infer_instance

/-- The stuck state reached from `σ`. -/
def toStuck (σ : State) : State := { σ with stuck := true }

/-- Advance the program counter. -/
def next (σ : State) : State := { σ with pc := σ.pc + 1 }

/-- Write an integer register, checking the word bound. -/
def setI (W : ℤ) (σ : State) (d : ℕ) (z : ℤ) : State :=
  if Fits W z then next { σ with ireg := Function.update σ.ireg d z } else toStuck σ

/-- Write a real register. -/
def setR (σ : State) (d : ℕ) (x : ℝ) : State :=
  next { σ with rreg := Function.update σ.rreg d x }

/-- One step of the machine with word bound `W`. -/
noncomputable def step (P : Program) (W : ℤ) (σ : State) : State :=
  if σ.halted || σ.stuck then σ else
  match P[σ.pc]? with
  | none => toStuck σ
  | some ins =>
    match ins with
    | .iconst d z => setI W σ d z
    | .iadd d a b => setI W σ d (σ.ireg a + σ.ireg b)
    | .isub d a b => setI W σ d (σ.ireg a - σ.ireg b)
    | .imul d a b => setI W σ d (σ.ireg a * σ.ireg b)
    | .idiv d a b => if σ.ireg b = 0 then toStuck σ else setI W σ d (σ.ireg a / σ.ireg b)
    | .iload d a =>
        if Fits W (σ.ireg a) then setI W σ d (σ.imem (σ.ireg a)) else toStuck σ
    | .istore a b =>
        if Fits W (σ.ireg a) then
          next { σ with imem := Function.update σ.imem (σ.ireg a) (σ.ireg b) }
        else toStuck σ
    | .ijle a b t => if σ.ireg a ≤ σ.ireg b then { σ with pc := t } else next σ
    | .jmp t => { σ with pc := t }
    | .rzero d => setR σ d 0
    | .radd d a b => setR σ d (σ.rreg a + σ.rreg b)
    | .rsub d a b => setR σ d (σ.rreg a - σ.rreg b)
    | .rmul d a b => setR σ d (σ.rreg a * σ.rreg b)
    | .rdiv d a b => if σ.rreg b = 0 then toStuck σ else setR σ d (σ.rreg a / σ.rreg b)
    | .rcopy d a => setR σ d (σ.rreg a)
    | .rload d a =>
        if Fits W (σ.ireg a) then setR σ d (σ.rmem (σ.ireg a)) else toStuck σ
    | .rstore a b =>
        if Fits W (σ.ireg a) then
          next { σ with rmem := Function.update σ.rmem (σ.ireg a) (σ.rreg b) }
        else toStuck σ
    | .rjlt a b t => if σ.rreg a < σ.rreg b then { σ with pc := t } else next σ
    | .rjeq a b t => if σ.rreg a = σ.rreg b then { σ with pc := t } else next σ
    | .halt => { σ with halted := true }

/-- The state after `t` steps. -/
noncomputable def run (P : Program) (W : ℤ) (σ : State) (t : ℕ) : State := (step P W)^[t] σ

/-- The initial state for integer input `inI` (memory cells `0, 1, …`) and real input `inR`
(real memory cells `0, 1, …`); every other cell and every register is `0`, the program counter is
`0`. -/
def load (inI : List ℤ) (inR : List ℝ) : State where
  pc := 0
  ireg := fun _ => 0
  imem := fun a => if h : 0 ≤ a ∧ a.toNat < inI.length then inI[a.toNat] else 0
  rreg := fun _ => 0
  rmem := fun a => if h : 0 ≤ a ∧ a.toNat < inR.length then inR[a.toNat] else 0
  halted := false
  stuck := false

/-- Integer output cell `j`: memory cell `-1 - j`. -/
def outI (σ : State) (j : ℕ) : ℤ := σ.imem (-1 - (j : ℤ))

/-- Real output cell `j`: real memory cell `-1 - j`. -/
def outR (σ : State) (j : ℕ) : ℝ := σ.rmem (-1 - (j : ℤ))

/-- From the input `(inI, inR)`, with word bound `W`, the program halts within `T` steps (some
`t ≤ T` reaches a halted state) and the output satisfies `Post`. -/
def HaltsWithin (P : Program) (W : ℤ) (inI : List ℤ) (inR : List ℝ) (T : ℝ)
    (Post : (ℕ → ℤ) → (ℕ → ℝ) → Prop) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ T ∧ (run P W (load inI inR) t).halted = true ∧
    (run P W (load inI inR) t).stuck = false ∧
    Post (outI (run P W (load inI inR) t)) (outR (run P W (load inI inR) t))

end Machine

end MinCostArbPacking.Main


