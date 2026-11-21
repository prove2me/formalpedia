-- Prove2me | Definitions.Def_SourceProof_a8df8d1e682dc608b5be8245
-- name    : SourceProof_a8df8d1e682dc608b5be8245
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:00:34.364738+00:00
-- url     : https://prove2.me/theorems/60bddad4-0851-4010-9762-9dcbdd526851
-- title:
--   LevyStochCalc source module: SourceProof_a8df8d1e682dc608b5be8245
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.condExp_jointChaosStep_mul` comes from the `LevyStochCalc.Driver.JointChaosStep` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointChaosStep_F000
import Definitions.Def_SourceProof_38d504a1087b78cbf737f4a0
import Definitions.Def_SourceProof_b5912c738affc5f69d2adbcb

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The joint chaos element of one step of a Lévy driver

For a Lévy driver, a coordinate `j`, a step `(a, b]` and a mark set `A`, the bidegree-`(n, m)`
element of the step is the product `H_n(ΔWʲ; b - a) C_m(N(B); ν̂(B))` of the degree-`n` Wiener
chaos element of the increment `ΔWʲ = Wʲ_b - Wʲ_a` and the degree-`m` Poisson chaos element of
the strip `B = (a, b] ×ˢ A`. Since `σ(W)` and `σ(N)` are independent, the expectation of a
product of a function of the increment and a function of the count factors, so the `L²` pairing
of two such elements is the product of the Brownian and the Poisson pairings,
`E[J_(n, m) J_(n', m')] = δ_(n n') δ_(m m') n! τ ^ n m! λ ^ m` for `τ = b - a` and
`λ = (b - a) ν(A)`. Distinct bidegrees are therefore orthogonal, and a fortiori so are distinct
total degrees `n + m`. The step tuple is independent of the joint filtration at `a`, so the
conditional pairing at that node is the same constant.

One Brownian coordinate and one mark set are covered: these are polynomials of the single
increment `ΔWʲ` and the single count `N(B)`, with no mark profile beyond the indicator of `A`.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointChaosStep` — the bidegree-`(n, m)` element of a step.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.indepFun_increment_count` — a Brownian increment of the driver
  is independent of a count of its Poisson random measure.
* `LevyStochCalc.Driver.LevyDriver.integral_increment_count_mul` — the expectation of a product
  of a function of an increment and a function of a count factors.
* `LevyStochCalc.Driver.LevyDriver.memLp_two_jointChaosStep` — square integrability.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStep_mul` —
  `E[J_(n, m) J_(n', m')] = δ_(n n') δ_(m m') n! τ ^ n m! λ ^ m`.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStep_mul_eq_zero_of_add_ne` — orthogonality
  across total degrees.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStep_mul_eq_zero` — orthogonality across
  bidegrees.
* `LevyStochCalc.Driver.LevyDriver.condExp_jointChaosStep_mul` — the conditional pairing at the
  node preceding the step.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

section Independence

variable {γ δ : Type*} [MeasurableSpace γ] [MeasurableSpace δ]

end Independence


theorem _root_.Prove2MeSourceProof.h_a8df8d1e682dc608b5be8245 (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    (hab : a < b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (n m n' m' : ℕ) :
    P[fun ω => D.jointChaosStep j n m a b A ω * D.jointChaosStep j n' m' a b A ω
        | D.filtration (a : ℝ)]
      =ᵐ[P] fun _ => (if n = n' then (n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n else 0)
        * (if m = m' then (m.factorial : ℝ)
            * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ m else 0) := by
  classical
  set B : Set (ℝ × E) := Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A with hBdef
  have hB : MeasurableSet B := measurableSet_Ioc.prod hA
  set C : Fin 1 → Set (ℝ × E) := fun _ => B with hC
  have hCm : ∀ k, MeasurableSet (C k) := fun _ => hB
  have hCs : ∀ k, C k ⊆ Set.Ioi (a : ℝ) ×ˢ Set.univ := fun _ x hx => ⟨hx.1.1, trivial⟩
  have hindep : Indep (D.stepSigma C (a : ℝ) (b : ℝ)) (D.filtration (a : ℝ)) P :=
    (_root_.Prove2MeSourceProof.h_b5912c738affc5f69d2adbcb D) C hCm a.coe_nonneg (by exact_mod_cast hab) hCs
  have hincr : Measurable[D.stepSigma C (a : ℝ) (b : ℝ)]
      (fun ω => (D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) :=
    Measurable.of_comap_le (le_sup_of_le_left (le_iSup (fun i => D.incrementSigma i a b) j))
  have hcount : Measurable[D.stepSigma C (a : ℝ) (b : ℝ)] (fun ω => D.N.N ω B) :=
    Measurable.of_comap_le (le_sup_of_le_right
      (le_iSup (fun k => D.regionSigma (C k)) (0 : Fin 1)))
  have hstep : ∀ p q : ℕ, Measurable[D.stepSigma C (a : ℝ) (b : ℝ)]
      (fun ω => D.jointChaosStep j p q a b A ω) := fun p q =>
    ((LevyStochCalc.Probability.measurable_wienerChaosStep p _).comp hincr).mul
      ((((LevyStochCalc.Probability.continuous_charlierScaled q _).measurable).comp
        ENNReal.measurable_toReal).comp hcount)
  have hmeas : StronglyMeasurable[D.stepSigma C (a : ℝ) (b : ℝ)]
      (fun ω => D.jointChaosStep j n m a b A ω * D.jointChaosStep j n' m' a b A ω) :=
    Measurable.stronglyMeasurable ((hstep n m).mul (hstep n' m'))
  have h := condExp_indep_eq (D.stepSigma_le C hCm (a : ℝ) (b : ℝ)) (D.filtration.le (a : ℝ))
    hmeas hindep
  rw [(_root_.Prove2MeSourceProof.h_38d504a1087b78cbf737f4a0 D) j hab.le hA hAν n m n' m'] at h
  exact h
end LevyDriver

end LevyStochCalc.Driver


