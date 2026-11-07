-- Prove2me | Definitions.Def_MatMulTimeLP_RealRAM
-- name    : MatMulTimeLP_RealRAM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:47:09.257655+00:00
-- url     : https://prove2.me/theorems/97b5656d-184a-415a-b8b2-63216be314a4
-- title:
--   The randomized real RAM: programs, runs, running time, tape law
-- statement:
--   The paper works in exact real arithmetic: "elementary operations, including square roots, take constant time", and "a standard Gaussian random variable can be sampled in constant time". This module makes that model a machine.
--
--   A **program** is a finite list of instructions acting on two banks of cells, reals $R:\mathbb N\to\mathbb R$ and indices $N:\mathbb N\to\mathbb N$. The instructions are: real constants, $+,-,\times,\div$ and $\sqrt{\cdot}$ on real cells; indirect load and store of real cells through an index cell; index constants, $+,-$ and indirect load and store on index cells; a comparison-and-jump on each bank; `gauss` and `unif`, which write the Gaussian and the uniform of the current time step; and `halt`.
--
--   The **tape** is a sequence $\omega\in(\mathbb R\times\mathbb R)^{\mathbb N}$ with independent coordinates, each an independent pair of a standard Gaussian and a uniform on $[0,1]$. A run starts with the input in $R[0],R[1],\dots$ and every other cell $0$. A run that halts at step $t$ has **running time** $t+1$, and a run that never halts has running time $+\infty$. The output is read from the cells after the input.
--
--   This is the cost model of every running-time claim of the mission.
--
--   **Formalization Note** Every instruction costs $1$, including reading an input cell. There is no floor, no real-to-index conversion, no bit operation and no index multiplication, because unit-cost floor on unbounded-precision reals would pack whole matrices into a single cell. The conventions $x/0=0$ and $\sqrt{x}=0$ for $x<0$ are harmless, since a program can test those cases first. A program counter past the end of the program acts as `halt`.
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Section 3, Computational Model, p.15; Algorithms 5 and 6, pp.35, 46 (uniform draws)

import Mathlib

namespace MatMulTimeLP

open MeasureTheory ProbabilityTheory

/-!
# The randomized real RAM

Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Section 3, "Computational Model", p.15: "exact real
arithmetic: we assume that elementary operations, including square roots, take constant time, and
that a standard Gaussian random variable can be sampled in constant time".

**Formalization Note** A deep-embedded machine with two banks of cells, reals `R : ℕ → ℝ` and
indices `N : ℕ → ℕ`. Every executed instruction costs `1`, including reading an input cell. There
is no floor, no real-to-index conversion, no bit operation and no index multiplication: unit-cost
floor on unbounded-precision reals would pack whole matrices into one cell. Lean's `x / 0 = 0` and
`√x = 0` for `x < 0` are harmless, because a program can test those cases with `rblt`. `nsub` is
truncated subtraction, and a program tests it with `nblt`. `rconst` takes any real literal.
Algorithms 5 and 6 of the paper also draw uniforms (p.35, p.46), hence `unif`. The tape has one
fresh Gaussian and one fresh uniform per time step, so independence holds by construction. A
program counter past the end of the program acts as `halt`.
-/

/-- An instruction of the randomized real RAM. `R[·]` and `N[·]` are the real and the index cells.
* `rconst i c`: `R[i] := c`.
* `radd/rsub/rmul/rdiv i j k`: `R[i] := R[j] ∘ R[k]`.
* `rsqrt i j`: `R[i] := √R[j]`.
* `rload i j`: `R[i] := R[N[j]]`; `rstore i j`: `R[N[i]] := R[j]`.
* `nconst i m`: `N[i] := m`; `nadd/nsub i j k`: `N[i] := N[j] ∘ N[k]`.
* `nload i j`: `N[i] := N[N[j]]`; `nstore i j`: `N[N[i]] := N[j]`.
* `rblt i j l`: if `R[i] < R[j]` go to `l`; `nblt i j l`: if `N[i] < N[j]` go to `l`.
* `gauss i`, `unif i`: `R[i] :=` the Gaussian, the uniform of the current time step.
* `halt`. -/
inductive Instr where
  | rconst (i : ℕ) (c : ℝ)
  | radd (i j k : ℕ)
  | rsub (i j k : ℕ)
  | rmul (i j k : ℕ)
  | rdiv (i j k : ℕ)
  | rsqrt (i j : ℕ)
  | rload (i j : ℕ)
  | rstore (i j : ℕ)
  | nconst (i m : ℕ)
  | nadd (i j k : ℕ)
  | nsub (i j k : ℕ)
  | nload (i j : ℕ)
  | nstore (i j : ℕ)
  | rblt (i j l : ℕ)
  | nblt (i j l : ℕ)
  | gauss (i : ℕ)
  | unif (i : ℕ)
  | halt

/-- A program: a finite list of instructions. -/
abbrev Program := List Instr

/-- A machine state: the program counter and the two banks of cells. -/
structure State where
  pc : ℕ
  R : ℕ → ℝ
  N : ℕ → ℕ

/-- The random tape: at time `t` the pair (Gaussian, uniform). -/
abbrev Tape := ℕ → ℝ × ℝ

/-- The initial state: the input in `R[0], R[1], …`, every other cell `0`, program counter `0`. -/
noncomputable def initState (input : List ℝ) : State :=
  ⟨0, fun i => input.getD i 0, fun _ => 0⟩

/-- The state `s` is halted under `P`: the current instruction is `halt`, or the program counter is
past the end of `P`. -/
def IsHalted (P : Program) (s : State) : Prop :=
  P[s.pc]? = none ∨ P[s.pc]? = some Instr.halt

/-- One step of `P` at time `t` on the tape `ω`. A halted state is unchanged. -/
noncomputable def step (P : Program) (ω : Tape) (t : ℕ) (s : State) : State :=
  match P[s.pc]? with
  | none => s
  | some Instr.halt => s
  | some (Instr.rconst i c) => ⟨s.pc + 1, Function.update s.R i c, s.N⟩
  | some (Instr.radd i j k) => ⟨s.pc + 1, Function.update s.R i (s.R j + s.R k), s.N⟩
  | some (Instr.rsub i j k) => ⟨s.pc + 1, Function.update s.R i (s.R j - s.R k), s.N⟩
  | some (Instr.rmul i j k) => ⟨s.pc + 1, Function.update s.R i (s.R j * s.R k), s.N⟩
  | some (Instr.rdiv i j k) => ⟨s.pc + 1, Function.update s.R i (s.R j / s.R k), s.N⟩
  | some (Instr.rsqrt i j) => ⟨s.pc + 1, Function.update s.R i (Real.sqrt (s.R j)), s.N⟩
  | some (Instr.rload i j) => ⟨s.pc + 1, Function.update s.R i (s.R (s.N j)), s.N⟩
  | some (Instr.rstore i j) => ⟨s.pc + 1, Function.update s.R (s.N i) (s.R j), s.N⟩
  | some (Instr.nconst i m) => ⟨s.pc + 1, s.R, Function.update s.N i m⟩
  | some (Instr.nadd i j k) => ⟨s.pc + 1, s.R, Function.update s.N i (s.N j + s.N k)⟩
  | some (Instr.nsub i j k) => ⟨s.pc + 1, s.R, Function.update s.N i (s.N j - s.N k)⟩
  | some (Instr.nload i j) => ⟨s.pc + 1, s.R, Function.update s.N i (s.N (s.N j))⟩
  | some (Instr.nstore i j) => ⟨s.pc + 1, s.R, Function.update s.N (s.N i) (s.N j)⟩
  | some (Instr.rblt i j l) => if s.R i < s.R j then ⟨l, s.R, s.N⟩ else ⟨s.pc + 1, s.R, s.N⟩
  | some (Instr.nblt i j l) => if s.N i < s.N j then ⟨l, s.R, s.N⟩ else ⟨s.pc + 1, s.R, s.N⟩
  | some (Instr.gauss i) => ⟨s.pc + 1, Function.update s.R i (ω t).1, s.N⟩
  | some (Instr.unif i) => ⟨s.pc + 1, Function.update s.R i (ω t).2, s.N⟩

/-- The state after `t` steps of `P` on `input` and the tape `ω`. -/
noncomputable def stateAt (P : Program) (input : List ℝ) (ω : Tape) : ℕ → State
  | 0 => initState input
  | t + 1 => step P ω t (stateAt P input ω t)

/-- The run halts at step `t`: `t` is the first time the state is halted. -/
def HaltsAt (P : Program) (input : List ℝ) (ω : Tape) (t : ℕ) : Prop :=
  IsHalted P (stateAt P input ω t) ∧ ∀ s < t, ¬ IsHalted P (stateAt P input ω s)

/-- The running time: for a run that halts at step `t` the `t` executed instructions plus the final
`halt`, so `t + 1`; `⊤` for a run that never halts. -/
noncomputable def haltTime (P : Program) (input : List ℝ) (ω : Tape) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : IsHalted P (stateAt P input ω t)), ((t + 1 : ℕ) : ℕ∞)

/-- The output vector of length `m` of the state after `t` steps: the cells from `input.length` on. -/
noncomputable def outputAt (P : Program) (input : List ℝ) (ω : Tape) (t m : ℕ) : Fin m → ℝ :=
  fun j => (stateAt P input ω t).R (input.length + j)

/-- The output matrix of shape `a × b` after `t` steps, read row by row from output position
`off` on. -/
noncomputable def outputMatAt (P : Program) (input : List ℝ) (ω : Tape) (t off a b : ℕ) :
    Matrix (Fin a) (Fin b) ℝ :=
  fun i j => (stateAt P input ω t).R (input.length + off + i * b + j)

/-- The uniform law on `[0, 1]`. -/
noncomputable def uniform01 : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance : IsProbabilityMeasure uniform01 :=
  ⟨by simp [uniform01]⟩

/-- The law of the tape: all coordinates independent, each coordinate an independent pair of a
standard Gaussian and a uniform on `[0, 1]`. -/
noncomputable def tapeLaw : Measure Tape :=
  Measure.infinitePi fun _ => (gaussianReal 0 1).prod uniform01

instance : IsProbabilityMeasure tapeLaw := by
  unfold tapeLaw; infer_instance

/-- A vector as a list, in coordinate order. -/
def vecToList {m : ℕ} (v : Fin m → ℝ) : List ℝ :=
  (List.finRange m).map v

/-- A matrix as a list, row by row. -/
def matToList {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) : List ℝ :=
  (List.finRange a).flatMap fun i => vecToList (M i)

end MatMulTimeLP


