-- Prove2me | Definitions.Def_MatrixSenseRank_Testing_Supplement_Computation
-- name    : MatrixSenseRank_Testing_Supplement_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:08:44.082699+00:00
-- url     : https://prove2.me/theorems/5db6ed66-25c0-4667-9e5b-6a08aa87522c
-- title:
--   Operational numerical recovery and Candès–Plan–Test
-- statement:
--   A numerical routine is a finite program of the published real random-access machine. Rational constants, real arithmetic, square roots, comparisons, indirect memory and fair coins are allowed; real powers are excluded. Each instruction costs one operation. Programs are required to halt uniformly within $K s^d$ operations, where $K,d$ are fixed and $s$ counts input-list lengths, integer dimensions and sample counts, and the logarithm of two plus the sum of absolute real inputs. Accuracy and its inverse are both supplied, so the requested precision is charged logarithmically. Inputs are exact reals; this convention does not assert Turing bit complexity for Gaussian observations.
--
--   Recovery reads dimensions, sample count, known $\sigma$, requested error $\delta$ and the complete row-major observations, and returns matrix entries from its output memory. Truncation reads a matrix and tolerance and returns two vectors whose outer product is a rank-at-most-one candidate. These are operational executions, with no success certificate assumed in their definitions.
--
--   For external accuracy $\varepsilon$, use $\rho=\varepsilon/\sqrt2$ and $\delta=\rho/8$. Algorithm 1 uses
--
--   $$T_1=\left\lceil C\max(n,m)(1+\sigma^2/\delta^2)\right\rceil,\qquad T_2=\left\lceil42(1+\sigma^2/\rho^2)^2\right\rceil.$$
--
--   Recovery is requested at error $\delta/2$ and numerical rank-one truncation at additive tolerance $\delta/2$; these finite tolerances reserve the slack in the paper's $\rho/4$ error bound. Independent coin tapes and independent training and validation batches are used. The decision accepts precisely when
--
--   $$\sum_{t=1}^{T_2}(y_t-\langle B,X_t\rangle_F)^2\le(\sigma^2+\rho^2/2)T_2.$$
--
--   The cost definition charges both routine executions and validation arithmetic, including the precision of intermediate outputs. The implementation relation connects this actual computation to a measurable Boolean kernel. Existence, halting, approximation properties and statistical guarantees are conclusions of the theorems, not axioms of these objects.
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, Matrix sensing meets property testing: Sample-optimal testing for low rank, STOC 2027 submission #380 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf, PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b; Proposition 12, Remark 13, Algorithm 1 and normalization paragraph, printed p. 22–26, PDF p. 23–27 (1-based).

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_MatrixSenseRank_Testing_Supplement_Optimization

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MatrixSenseRank.Testing.Supplement

/-- Arithmetic interpretation of polynomial time: rational constants, +,-,*,/,sqrt,
comparisons, memory and fair coins. The more powerful real-power instruction is excluded. -/
def ArithmeticProgram (P : PNormReg.Program) : Prop :=
  PNormReg.Admissible P ∧ ∀ op ∈ P, match op with
    | .rpow _ _ _ => False
    | _ => True

/-- Row-major order, including every design coordinate and its label. -/
def encodeSamples {n m T : ℕ} (s : Fin T → Observation n m) : List ℝ :=
  (List.finRange T).flatMap fun t =>
    ((List.finRange n).flatMap fun i => (List.finRange m).map fun j => (s t).1 i j) ++ [(s t).2]

def encodeMatrix {n m : ℕ} (A : Mat n m) : List ℝ :=
  (List.finRange n).flatMap fun i => (List.finRange m).map fun j => A i j

/-- Numerical accuracy and data magnitude count logarithmically. This is a continuous-input
operation model, not Turing complexity of an exact Gaussian real. The inverse tolerance is
included, so arbitrarily small absolute requested error is never free. -/
noncomputable def numericSize (ints : List ℤ) (reals : List ℝ) : ℕ :=
  1 + ints.length + reals.length + (ints.map Int.natAbs).sum +
    ⌈Real.log (2 + (reals.map abs).sum)⌉₊

/-- A uniform polynomial number of individual machine instructions. -/
noncomputable def workBound (K d : ℕ) (ints : List ℤ) (reals : List ℝ) : ℕ :=
  K * (numericSize ints reals) ^ d

noncomputable def machineState (P : PNormReg.Program) (K d : ℕ)
    (ints : List ℤ) (reals : List ℝ) (ω : ℕ → Bool) : PNormReg.State :=
  PNormReg.run P (PNormReg.initState ints reals) ω (workBound K d ints reals)

/-- Operational halting, independent of every statistical correctness claim. -/
def PolynomialHalting (P : PNormReg.Program) (K d : ℕ) : Prop :=
  ArithmeticProgram P ∧ 0 < K ∧
    ∀ (ints : List ℤ) (reals : List ℝ) (ω : ℕ → Bool),
      (machineState P K d ints reals ω).halted = true

/-- The inverse accuracy is an auxiliary input so numericSize charges its precision.
It conveys no hidden-target information. -/
noncomputable def recoveryInputs {n m T : ℕ} (σ δ : ℝ) (s : Fin T → Observation n m) : List ℝ :=
  [σ, δ, δ⁻¹] ++ encodeSamples s

noncomputable def recover {n m T : ℕ} (P : PNormReg.Program) (K d : ℕ)
    (σ δ : ℝ) (s : Fin T → Observation n m) (ω : ℕ → Bool) : Mat n m :=
  let state := machineState P K d [(n : ℤ), (m : ℤ), (T : ℤ)] (recoveryInputs σ δ s) ω
  fun i j => state.core.mem (-1 - ((i.val * m + j.val : ℕ) : ℤ))

/-- The truncation program outputs n left and m right coordinates in negative memory.
An outer product ensures rank at most one on every input, without a certificate. -/
noncomputable def numericalTruncation {n m : ℕ} (Q : PNormReg.Program) (K d : ℕ)
    (tol : ℝ) (M : Mat n m) (ω : ℕ → Bool) : Mat n m :=
  let state := machineState Q K d [(n : ℤ), (m : ℤ)] ([tol, tol⁻¹] ++ encodeMatrix M) ω
  fun i j => state.core.mem (-1 - (i.val : ℤ)) * state.core.mem (-1 - ((n + j.val : ℕ) : ℤ))

noncomputable def trainingCount (C : ℝ) (n m : ℕ) (σ ρ : ℝ) : ℕ :=
  ⌈C * max n m * (1 + σ ^ 2 / (ρ / 8) ^ 2)⌉₊

noncomputable def validationCount (σ ρ : ℝ) : ℕ := ⌈42 * (1 + σ ^ 2 / ρ ^ 2) ^ 2⌉₊

/-- Algorithm 1 with internal rho=epsilon/sqrt(2). Reserve half of delta=rho/8 for
numerical recovery and half for rank-one truncation. Even approximate routines then give
||B-A|| <= 3delta/2 < rho/4 on the good recovery event. Independent tapes and sample batches. -/
noncomputable def candesPlanDecision {n m : ℕ} (P Q : PNormReg.Program) (K d : ℕ)
    (C σ ε : ℝ)
    (s : Fin (trainingCount C n m σ (ε / Real.sqrt 2) +
      validationCount σ (ε / Real.sqrt 2)) → Observation n m)
    (ω : (ℕ → Bool) × (ℕ → Bool)) : Bool := by
  classical
  let ρ := ε / Real.sqrt 2
  let t₁ := trainingCount C n m σ ρ
  let t₂ := validationCount σ ρ
  let train : Fin t₁ → Observation n m := fun i => s ⟨i.val, by dsimp [t₁, t₂, ρ] at *; omega⟩
  let validate : Fin t₂ → Observation n m := fun i => s ⟨t₁ + i.val, by dsimp [t₁, t₂, ρ] at *; omega⟩
  let M := recover P K d σ ((ρ / 8) / 2) train ω.1
  let B := numericalTruncation Q K d ((ρ / 8) / 2) M ω.2
  exact decide ((∑ i, ((validate i).2 - frobeniusInner B (validate i).1) ^ 2) ≤
    (σ ^ 2 + ρ ^ 2 / 2) * t₂)

/-- A bound on every executed routine instruction plus the scalar scan/validation work.
This exposes the composition cost: a large intermediate output cannot make its second-stage
precision cost free. Ceilings can be implemented by counting up to the requested batch size. -/
noncomputable def candesPlanWork {n m : ℕ} (P : PNormReg.Program) (K d : ℕ)
    (C σ ε : ℝ)
    (s : Fin (trainingCount C n m σ (ε / Real.sqrt 2) +
      validationCount σ (ε / Real.sqrt 2)) → Observation n m)
    (ω : ℕ → Bool) : ℕ := by
  let ρ := ε / Real.sqrt 2
  let t₁ := trainingCount C n m σ ρ
  let t₂ := validationCount σ ρ
  let train : Fin t₁ → Observation n m := fun i =>
    s ⟨i.val, by dsimp [t₁, t₂, ρ] at *; omega⟩
  let tol := (ρ / 8) / 2
  let M := recover P K d σ tol train ω
  exact workBound K d [(n : ℤ), (m : ℤ), (t₁ : ℤ)] (recoveryInputs σ tol train) +
    workBound K d [(n : ℤ), (m : ℤ)] ([tol, tol⁻¹] ++ encodeMatrix M) +
    100 * (1 + n * m) * (1 + t₁ + t₂)

/-- Connect the finite operational algorithm to a measurable probability kernel.
No correctness or existence of a kernel is assumed by the definition. -/
def ImplementsCandesPlan {n m : ℕ} (P Q : PNormReg.Program) (K d : ℕ) (C σ ε : ℝ)
    (test : StatisticalTest (Observation n m)
      (trainingCount C n m σ (ε / Real.sqrt 2) + validationCount σ (ε / Real.sqrt 2))) : Prop :=
  ∀ s, test.accept s = ∫ ω,
    (if candesPlanDecision P Q K d C σ ε s ω then (1 : ℝ) else 0)
      ∂PNormReg.coinTape.prod PNormReg.coinTape

end MatrixSenseRank.Testing.Supplement


