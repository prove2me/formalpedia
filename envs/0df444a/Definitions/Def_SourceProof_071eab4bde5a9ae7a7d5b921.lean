-- Prove2me | Definitions.Def_SourceProof_071eab4bde5a9ae7a7d5b921
-- name    : SourceProof_071eab4bde5a9ae7a7d5b921
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:17:58.546171+00:00
-- url     : https://prove2.me/theorems/d6195233-49fc-4a8d-9732-ed292b5cef54
-- title:
--   LevyStochCalc source module: SourceProof_071eab4bde5a9ae7a7d5b921
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_sub_pow_four_le` comes from the `LevyStochCalc.Brownian.ItoIncrementMomentBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F002
import Definitions.Def_SourceProof_0895508398bff4a45b14f57f

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

section ThirdMoment

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_071eab4bde5a9ae7a7d5b921 {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MeasureTheory.Integrable (fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4) P
      ∧ ∫ ω, (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4 ∂P
        ≤ (6 + gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2 := by
  have hmeas := LevyStochCalc.Brownian.Ito.measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq a b
  have hbound := _root_.Prove2MeSourceProof.h_0895508398bff4a45b14f57f W ℱ hℱ H hm hp hq
    hC0 hCH ha hab
  have hpt : ∀ ω : Ω, ENNReal.ofReal ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4)
      = (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 4 := by
    have key : ∀ x : ℝ, ENNReal.ofReal (x ^ 4) = (‖x‖₊ : ℝ≥0∞) ^ 4 := by
      intro x
      have h1 : (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal |x| := by
        rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
        exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))
      rw [h1, ← ENNReal.ofReal_pow (abs_nonneg _), ← abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]
    exact fun ω => key _
  have hnn : ∀ ω : Ω, (0 : ℝ) ≤ (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4 := fun ω => by positivity
  have hint : MeasureTheory.Integrable
      (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4) P := by
    refine LevyStochCalc.Brownian.Ito.integrable_of_lintegral_nnnorm_lt_top
      (hmeas.pow_const 4).aestronglyMeasurable ?_
    have hrw : ∀ ω : Ω, ((‖(LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4‖₊ : ℝ≥0∞))
        = (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 4 := by
      intro ω
      rw [nnnorm_pow, ENNReal.coe_pow]
    simp_rw [hrw]
    exact lt_of_le_of_lt hbound (by simp)
  have hKnn : (0 : ℝ) ≤ (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith [LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg]) (by positivity))
      (by positivity)
  refine ⟨hint, LevyStochCalc.Brownian.Ito.integral_le_of_lintegral_ofReal_le hint hnn hKnn ?_⟩
  simp_rw [hpt]
  exact hbound
end ThirdMoment

end LevyStochCalc.Brownian.Ito


