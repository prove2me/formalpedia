-- Prove2me | Definitions.Def_SourceProof_4ef3e5b73189336215f644cf
-- name    : SourceProof_4ef3e5b73189336215f644cf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:22:36.43617+00:00
-- url     : https://prove2.me/theorems/7777b8b0-b816-48bf-81ff-c17ce214fb23
-- title:
--   LevyStochCalc source module: SourceProof_4ef3e5b73189336215f644cf
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_abs_sub_pow_three_le` comes from the `LevyStochCalc.Brownian.ItoIncrementMomentBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F002
import Definitions.Def_SourceProof_071eab4bde5a9ae7a7d5b921
import Definitions.Def_SourceProof_9a9fab4277e23ec64788cbe8

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

theorem _root_.Prove2MeSourceProof.h_4ef3e5b73189336215f644cf {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MeasureTheory.Integrable (fun ω => |stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω| ^ 3) P
      ∧ ∫ ω, |stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω| ^ 3 ∂P
        ≤ (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * ((b - a) * Real.sqrt (b - a)) := by
  have hmeas := LevyStochCalc.Brownian.Ito.measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq a b
  obtain ⟨h2int, h2le⟩ := _root_.Prove2MeSourceProof.h_9a9fab4277e23ec64788cbe8 W ℱ hℱ H hm hp hq hC0 hCH ha hab
  obtain ⟨h4int, h4le⟩ := _root_.Prove2MeSourceProof.h_071eab4bde5a9ae7a7d5b921 W ℱ hℱ H hm hp hq hC0 hCH ha hab
  have hba : (0 : ℝ) < b - a := by linarith
  set lam : ℝ := Real.sqrt (b - a) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.mpr hba
  have hlamsq : lam ^ 2 = b - a := Real.sq_sqrt hba.le
  -- pointwise Young inequality `2λ|y|³ ≤ λ²y² + y⁴`
  have hyoung : ∀ y : ℝ, |y| ^ 3 ≤ (lam ^ 2 * y ^ 2 + y ^ 4) / (2 * lam) := by
    intro y
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * lam)]
    have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
    have hy3 : |y| * y ^ 2 = |y| ^ 3 := by rw [← hy2]; ring
    have hid : (lam * |y| - y ^ 2) ^ 2
        = lam ^ 2 * |y| ^ 2 - 2 * lam * (|y| * y ^ 2) + y ^ 4 := by ring
    rw [hy2, hy3] at hid
    linarith [sq_nonneg (lam * |y| - y ^ 2), hid]
  have hdomint : MeasureTheory.Integrable
      (fun ω => (lam ^ 2 * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
        + (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4) / (2 * lam)) P :=
    ((h2int.const_mul (lam ^ 2)).add h4int).div_const _
  have hint3 : MeasureTheory.Integrable
      (fun ω => |LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω| ^ 3) P := by
    refine hdomint.mono ((hmeas.abs.pow_const 3).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ |stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω| ^ 3)]
    refine (hyoung _).trans (le_abs_self _)
  refine ⟨hint3, ?_⟩
  calc ∫ ω, |LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω| ^ 3 ∂P
      ≤ ∫ ω, (lam ^ 2 * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
          + (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4) / (2 * lam) ∂P :=
        MeasureTheory.integral_mono hint3 hdomint (fun ω => hyoung _)
    _ = (lam ^ 2 * (∫ ω, (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2 ∂P)
          + ∫ ω, (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4 ∂P) / (2 * lam) := by
        rw [MeasureTheory.integral_div,
          MeasureTheory.integral_add (h2int.const_mul _) h4int,
          MeasureTheory.integral_const_mul]
    _ ≤ (lam ^ 2 * (C ^ 2 * (b - a))
          + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) / (2 * lam) := by
        gcongr
    _ = (C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2 * ((b - a) * lam) := by
        rw [hlamsq]
        field_simp
        rw [hlamsq]
        ring
end ThirdMoment

end LevyStochCalc.Brownian.Ito


