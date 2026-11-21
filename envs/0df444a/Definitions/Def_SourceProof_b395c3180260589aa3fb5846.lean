-- Prove2me | Definitions.Def_SourceProof_b395c3180260589aa3fb5846
-- name    : SourceProof_b395c3180260589aa3fb5846
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:33:18.713055+00:00
-- url     : https://prove2.me/theorems/6abbc8a1-2df1-4ace-b11d-e37814043e71
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Driver.LevyDriver.memLp_two_jointChaosStep
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


theorem _root_.Prove2MeSourceProof.h_b395c3180260589aa3fb5846 (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    (hab : a ≤ b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (n m : ℕ) :
    MemLp (D.jointChaosStep j n m a b A) 2 P := by
  have hB : MeasurableSet (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) := measurableSet_Ioc.prod hA
  have hfin : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ≠ ⊤ := by
    rw [LevyStochCalc.Poisson.referenceIntensity, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc]
    refine ENNReal.mul_ne_top (ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_left)) hAν
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hW : Integrable (fun ω => LevyStochCalc.Probability.wienerChaosStep n (b - a)
      ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) ^ 2) P := by
    simpa only [pow_two] using
      LevyStochCalc.Brownian.BrownianMotion.integrable_wienerChaosStep_increment_mul (D.W.W j) a b hab n n
  have hN : Integrable (fun ω =>
      LevyStochCalc.Poisson.poissonChaosStep D.N m (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ω ^ 2) P := by
    simpa only [pow_two] using LevyStochCalc.Poisson.integrable_poissonChaosStep_mul D.N hB hfin m m
  have hcomp : IndepFun
      (fun ω => LevyStochCalc.Probability.wienerChaosStep n (b - a)
        ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) ^ 2)
      (fun ω => LevyStochCalc.Poisson.poissonChaosStep D.N m (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ω ^ 2) P :=
    (D.indepFun_increment_count j (a : ℝ) (b : ℝ) hB).comp
      ((LevyStochCalc.Probability.measurable_wienerChaosStep n _).pow_const 2)
      ((((LevyStochCalc.Probability.continuous_charlierScaled m _).measurable).comp
        ENNReal.measurable_toReal).pow_const 2)
  refine (memLp_two_iff_integrable_sq
    (D.measurable_jointChaosStep j n m a b hA).aestronglyMeasurable).2 ?_
  have := hcomp.integrable_mul hW hN
  simp only [LevyStochCalc.Driver.LevyDriver.jointChaosStep, mul_pow]
  exact this
end LevyDriver

end LevyStochCalc.Driver


