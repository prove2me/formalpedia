-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F001
-- name    : LevyStochCalc_Brownian_ItoIncrementMomentBounds_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:12:49.396468+00:00
-- url     : https://prove2.me/theorems/64689884-c62b-4dda-9176-c960ac9e4901
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoIncrementMomentBounds
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoIncrementMomentBounds. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F000
import Definitions.Def_LevyStochCalc_Probability_Progressive_F001

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

/-- Restricting an integrand to `(a, b]` preserves joint measurability. -/
theorem measurable_uncurry_indicator_Ioc_mul (H : Ω → ℝ → ℝ)
    (hm : Measurable (Function.uncurry H)) (a b : ℝ) :
    Measurable (Function.uncurry fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s) :=
  (((measurable_const.indicator measurableSet_Ioc).comp measurable_snd)).mul hm
/-- Restricting an integrand to `(a, b]` preserves progressive measurability. -/
theorem progressivelyMeasurable_indicator_Ioc_mul
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (H : Ω → ℝ → ℝ)
    (hp : Probability.ProgressivelyMeasurable ℱ H) (a b : ℝ) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s :=
  (progressivelyMeasurable_of_time ℱ (measurable_const.indicator measurableSet_Ioc)).mul hp
/-- Restricting an integrand to `(a, b]` cannot increase its `L²` mass. -/
theorem abs_indicator_Ioc_mul_le {P : Measure Ω} [IsProbabilityMeasure P] (H : Ω → ℝ → ℝ)
    (a b : ℝ) (ω : Ω) (s : ℝ) :
    |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s| ≤ |H ω s| := by
  by_cases hs : s ∈ Set.Ioc a b
  · rw [Set.indicator_of_mem hs, one_mul]
  · rw [Set.indicator_of_notMem hs, zero_mul, abs_zero]
    exact abs_nonneg _
/-- Restricting an integrand to `(a, b]` preserves square integrability. -/
theorem lintegral_sq_indicator_Ioc_mul_lt_top {P : Measure Ω} [IsProbabilityMeasure P]
    (H : Ω → ℝ → ℝ)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (a b : ℝ) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T hT
  refine lt_of_le_of_lt ?_ (hq T hT)
  refine lintegral_mono fun ω => lintegral_mono fun s => ?_
  refine pow_le_pow_left' (ENNReal.coe_le_coe.mpr ?_) 2
  rw [← NNReal.coe_le_coe]
  simpa [Real.norm_eq_abs] using abs_indicator_Ioc_mul_le (P := P) H a b ω s
end IncrementBound

section ThirdMoment

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end ThirdMoment

end LevyStochCalc.Brownian.Ito


