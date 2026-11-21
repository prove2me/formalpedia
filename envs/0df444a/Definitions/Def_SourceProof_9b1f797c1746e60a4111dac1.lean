-- Prove2me | Definitions.Def_SourceProof_9b1f797c1746e60a4111dac1
-- name    : SourceProof_9b1f797c1746e60a4111dac1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:16:44.243535+00:00
-- url     : https://prove2.me/theorems/f01f024e-1f58-4351-9f73-2b1eb85bd484
-- title:
--   LevyStochCalc source module: SourceProof_9b1f797c1746e60a4111dac1
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_sub_sq_le` comes from the `LevyStochCalc.Brownian.ItoIncrementMomentBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F001
import Definitions.Def_SourceProof_371bbffaec7b2a5d68568212
import Definitions.Def_SourceProof_7aea30f549f53f05062f1907

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

include hℱ in

theorem _root_.Prove2MeSourceProof.h_9b1f797c1746e60a4111dac1
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (C ^ 2 * (b - a)) := by
  classical
  have hb : (0 : ℝ) < b := lt_of_le_of_lt ha hab
  have hFle : ∀ (ω : Ω) (s : ℝ),
      |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s| ≤ |H ω s| :=
    fun ω s => LevyStochCalc.Brownian.Ito.abs_indicator_Ioc_mul_le (P := P) H a b ω s
  have hmF := LevyStochCalc.Brownian.Ito.measurable_uncurry_indicator_Ioc_mul H hm a b
  have hpF := LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indicator_Ioc_mul ℱ H hp a b
  have hqF := LevyStochCalc.Brownian.Ito.lintegral_sq_indicator_Ioc_mul_lt_top (P := P) H hq a b
  have hloc := _root_.Prove2MeSourceProof.h_371bbffaec7b2a5d68568212 W ℱ hℱ H hm hp hq ha hab hmF hpF hqF hb
  rw [min_self, min_eq_left hab.le] at hloc
  have hcongr : ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s)
          hmF hpF hqF b ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hloc] with ω hω
    rw [hω]
  rw [hcongr, _root_.Prove2MeSourceProof.h_7aea30f549f53f05062f1907 W ℱ hℱ _ hmF hpF hqF hb]
  -- the restricted integrand has `L²` mass at most `C²(b − a)` on every path
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
      ≤ ENNReal.ofReal (C ^ 2 * (b - a)) := by
    intro ω
    have hptw : ∀ s : ℝ,
        (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2
          ≤ (Set.Ioc a b).indicator (fun _ => ENNReal.ofReal (C ^ 2)) s := by
      intro s
      by_cases hs : s ∈ Set.Ioc a b
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, one_mul]
        have h1 : (‖H ω s‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal C := by
          rw [ENNReal.ofReal_eq_coe_nnreal hC0]
          refine ENNReal.coe_le_coe.mpr ?_
          rw [← NNReal.coe_le_coe]
          simpa [Real.norm_eq_abs] using hCH ω s
        calc (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal C ^ 2 := pow_le_pow_left' h1 2
          _ = ENNReal.ofReal (C ^ 2) := (ENNReal.ofReal_pow hC0 2).symm
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, zero_mul]
        simp
    calc ∫⁻ s in Set.Icc (0 : ℝ) b,
          (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
        ≤ ∫⁻ s in Set.Icc (0 : ℝ) b,
            (Set.Ioc a b).indicator (fun _ => ENNReal.ofReal (C ^ 2)) s ∂volume :=
          lintegral_mono hptw
      _ ≤ ∫⁻ s, (Set.Ioc a b).indicator (fun _ => ENNReal.ofReal (C ^ 2)) s ∂volume :=
          MeasureTheory.setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (C ^ 2) * volume (Set.Ioc a b) := by
          rw [lintegral_indicator measurableSet_Ioc, MeasureTheory.setLIntegral_const]
      _ = ENNReal.ofReal (C ^ 2 * (b - a)) := by
          rw [Real.volume_Ioc, ← ENNReal.ofReal_mul (by positivity)]
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ _ω : Ω, ENNReal.ofReal (C ^ 2 * (b - a)) ∂P := lintegral_mono hinner
    _ = ENNReal.ofReal (C ^ 2 * (b - a)) := by simp
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


