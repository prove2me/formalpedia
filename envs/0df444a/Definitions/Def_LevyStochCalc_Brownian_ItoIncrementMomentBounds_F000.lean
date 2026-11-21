-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F000
-- name    : LevyStochCalc_Brownian_ItoIncrementMomentBounds_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:10:46.863228+00:00
-- url     : https://prove2.me/theorems/78c91a60-1791-4f02-a015-3df5be3cc1ab
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoIncrementMomentBounds
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoIncrementMomentBounds. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentRestrict_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentRestrict_F001

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

/-- A process depending only on time is progressively measurable as soon as it is Borel. -/
theorem progressivelyMeasurable_of_time {g : ℝ → ℝ} (hg : Measurable g) :
    Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) s => g s) := by
  intro t
  have h : Measurable[@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance]
      (fun p : Ω × ℝ => (Set.Iic t).indicator g p.2) :=
    (hg.indicator measurableSet_Iic).comp measurable_snd
  exact h.stronglyMeasurable
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


