-- Prove2me | Definitions.Def_SourceProof_38d504a1087b78cbf737f4a0
-- name    : SourceProof_38d504a1087b78cbf737f4a0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:34:11.310342+00:00
-- url     : https://prove2.me/theorems/bec658a4-92b2-4cad-ae33-426b39716638
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Driver.LevyDriver.integral_jointChaosStep_mul
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointChaosStep_F000

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


theorem _root_.Prove2MeSourceProof.h_38d504a1087b78cbf737f4a0 (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    (hab : a ≤ b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (n m n' m' : ℕ) :
    ∫ ω, D.jointChaosStep j n m a b A ω * D.jointChaosStep j n' m' a b A ω ∂P
      = (if n = n' then (n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n else 0)
        * (if m = m' then (m.factorial : ℝ)
            * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ m else 0) := by
  classical
  set B : Set (ℝ × E) := Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A with hBdef
  have hB : MeasurableSet B := measurableSet_Ioc.prod hA
  set lam : ℝ := (LevyStochCalc.Poisson.referenceIntensity ν B).toReal with hlam
  set f : ℝ → ℝ := fun x => LevyStochCalc.Probability.wienerChaosStep n (b - a) x
    * LevyStochCalc.Probability.wienerChaosStep n' (b - a) x with hf
  set g : ℝ≥0∞ → ℝ := fun y => LevyStochCalc.Probability.charlierScaled m lam y.toReal
    * LevyStochCalc.Probability.charlierScaled m' lam y.toReal with hg
  have hfm : Measurable f :=
    (LevyStochCalc.Probability.measurable_wienerChaosStep n _).mul (LevyStochCalc.Probability.measurable_wienerChaosStep n' _)
  have hgm : Measurable g :=
    (((LevyStochCalc.Probability.continuous_charlierScaled m lam).measurable).comp
        ENNReal.measurable_toReal).mul
      (((LevyStochCalc.Probability.continuous_charlierScaled m' lam).measurable).comp
        ENNReal.measurable_toReal)
  have hrw : ∀ ω : Ω, (LevyStochCalc.Driver.LevyDriver.jointChaosStep D) j n m a b A ω * (LevyStochCalc.Driver.LevyDriver.jointChaosStep D) j n' m' a b A ω
      = f ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) * g (D.N.N ω B) := by
    intro ω
    simp only [LevyStochCalc.Driver.LevyDriver.jointChaosStep, hf, hg, LevyStochCalc.Poisson.poissonChaosStep, hlam]
    ring
  rw [show (∫ ω, (LevyStochCalc.Driver.LevyDriver.jointChaosStep D) j n m a b A ω * (LevyStochCalc.Driver.LevyDriver.jointChaosStep D) j n' m' a b A ω ∂P)
      = ∫ ω, f ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) * g (D.N.N ω B) ∂P from
    integral_congr_ae (Filter.Eventually.of_forall hrw)]
  rw [D.integral_increment_count_mul j (a : ℝ) (b : ℝ) hB hfm hgm]
  congr 1
  · rw [LevyStochCalc.Brownian.BrownianMotion.integral_wienerChaosStep_increment_mul (D.W.W j) a b hab n n',
      NNReal.coe_sub hab]
  · have := LevyStochCalc.Poisson.integral_poissonChaosStep_strip_mul D.N (a := (a : ℝ)) (b := (b : ℝ))
      a.coe_nonneg (by exact_mod_cast hab) hA hAν m m'
    simpa only [LevyStochCalc.Poisson.poissonChaosStep, hg, hlam, hBdef] using this
end LevyDriver

end LevyStochCalc.Driver


