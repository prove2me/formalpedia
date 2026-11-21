-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F002
-- name    : LevyStochCalc_Brownian_ItoIncrementMomentBounds_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:11:32.874049+00:00
-- url     : https://prove2.me/theorems/3dc1026f-a469-443e-80d5-9f2883e47c58
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoIncrementMomentBounds
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoIncrementMomentBounds. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentRestrict_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentRestrict_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of an increment of the Itô integral

The fourth moment of `∫_a^b H dW` for an integrand bounded by `C` is at most
`(6 + c)·C⁴·(b − a)²`, with `c` the fourth moment of the standard Gaussian, the second moment is
at most `C²·(b − a)`, and interpolating between the two by `2λ|y|³ ≤ λ²y² + y⁴` at `λ = √(b − a)`
bounds the third absolute moment. The fourth-moment bound is the per-tile variance budget of
`LevyStochCalc.Brownian.Ito.SimplePredictable.varClock` applied to simple approximants of
`1_{(a, b]}·H` that themselves vanish off `(a, b]`.

## Main statements

* `lintegral_stochasticIntegralBrownian_pow_four_le_Ioc` — the fourth-moment bound for an
  integrand supported in `(a, b]`.
* `lintegral_stochasticIntegralBrownian_sub_pow_four_le` —
  `𝔼|∫_a^b H dW|⁴ ≤ (6 + c)·C⁴·(b − a)²` for an integrand bounded by `C`.
* `lintegral_stochasticIntegralBrownian_sub_sq_le` — `𝔼|∫_a^b H dW|² ≤ C²·(b − a)`.
* `integral_abs_sub_pow_three_le` —
  `𝔼|∫_a^b H dW|³ ≤ ((C² + (6 + c)C⁴)/2)·(b − a)·√(b − a)`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section IncrementBound

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end IncrementBound

/-- A measurable function with finite `lintegral` of its norm is integrable. -/
theorem integrable_of_lintegral_nnnorm_lt_top {P : Measure Ω} {f : Ω → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f P)
    (h : ∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞) ∂P < ⊤) : MeasureTheory.Integrable f P := by
  refine ⟨hf, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  simpa only [enorm_eq_nnnorm] using h
/-- A pointwise-nonnegative integrand is bounded through its `lintegral`. -/
theorem integral_le_of_lintegral_ofReal_le {P : Measure Ω} {f : Ω → ℝ}
    (hint : MeasureTheory.Integrable f P) (hnn : ∀ ω, 0 ≤ f ω) {K : ℝ} (hK : 0 ≤ K)
    (h : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal K) : ∫ ω, f ω ∂P ≤ K := by
  rw [← ENNReal.ofReal_le_ofReal_iff hK,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]
  exact h
section ThirdMoment

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ in
/-- The increment of the `L²` Itô integral is measurable. -/
theorem measurable_sub_stochasticIntegralBrownian (a b : ℝ) :
    Measurable fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω :=
  (((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq b).mono
      (ℱ.le b)).measurable).sub
    (((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq a).mono
      (ℱ.le a)).measurable)
end ThirdMoment

end LevyStochCalc.Brownian.Ito


