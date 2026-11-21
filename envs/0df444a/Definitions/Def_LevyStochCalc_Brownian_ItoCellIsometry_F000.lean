-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoCellIsometry_F000
-- name    : LevyStochCalc_Brownian_ItoCellIsometry_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:14:42.583232+00:00
-- url     : https://prove2.me/theorems/71abf034-5b37-454b-972c-c96aa893e6fb
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoCellIsometry
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoCellIsometry. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F002
import Definitions.Def_SourceProof_371bbffaec7b2a5d68568212
import Definitions.Def_SourceProof_7aea30f549f53f05062f1907

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô isometry on a cell

For `0 ≤ a < b` the increment of the `L²` Itô integral across the cell `(a, b]` has squared
`L²(P)`-mass equal to the `L²` mass of the integrand over that cell:

  `𝔼‖∫_0^b H dW − ∫_0^a H dW‖² = 𝔼 ∫_{(a, b]} ‖H_s‖² ds`.

This is the horizon isometry `isometry_stochasticIntegralBrownian` applied to the integrand
`1_{(a, b]}·H`, whose integral at horizon `b` is the increment across `(a, b]`.

## Main statements

* `lintegral_sq_stochasticIntegralBrownian_indicator_Ioc` — the isometry for the integrand
  restricted to `(a, b]`.
* `lintegral_sq_stochasticIntegralBrownian_sub` — the isometry with the increment written as a
  difference of the horizon-`b` and horizon-`a` integrals of `H`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section CellIsometry

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

omit [MeasurableSpace Ω] in
/-- The squared modulus of an integrand restricted to `(a, b]` is the indicator of `(a, b]`
applied to the squared modulus of the integrand. -/
theorem nnnorm_sq_indicator_Ioc_mul (H : Ω → ℝ → ℝ) (a b : ℝ) (ω : Ω) (s : ℝ) :
    (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2
      = (Set.Ioc a b).indicator (fun u => (‖H ω u‖₊ : ℝ≥0∞) ^ 2) s := by
  by_cases hs : s ∈ Set.Ioc a b
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, one_mul]
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, zero_mul]
    simp
omit [MeasurableSpace Ω] in
/-- For `0 ≤ a` the `L²` mass on the horizon `[0, b]` of an integrand restricted to `(a, b]` is
the `L²` mass of the integrand over the cell `(a, b]`. -/
theorem setLIntegral_Icc_nnnorm_sq_indicator_Ioc_mul (H : Ω → ℝ → ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (ω : Ω) :
    ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = ∫⁻ s in Set.Ioc a b, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
  have hsub : Set.Ioc a b ⊆ Set.Icc (0 : ℝ) b := fun s hs => ⟨le_trans ha hs.1.le, hs.2⟩
  simp_rw [nnnorm_sq_indicator_Ioc_mul H a b ω]
  rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_self_of_subset_left hsub]
include hℱ in
/-- **Itô isometry on a cell, restricted-integrand form.** For `0 ≤ a < b` the integral of
`1_{(a, b]}·H` at horizon `b` has squared `L²(P)`-mass `𝔼 ∫_{(a, b]} ‖H_s‖² ds`. -/
theorem lintegral_sq_stochasticIntegralBrownian_indicator_Ioc
    (H : Ω → ℝ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (him : Measurable (Function.uncurry fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s))
    (hip : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s)
    (hiq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s)
        him hip hiq b ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Ioc a b, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hb : (0 : ℝ) < b := lt_of_le_of_lt ha hab
  rw [_root_.Prove2MeSourceProof.h_7aea30f549f53f05062f1907 W ℱ hℱ _ him hip hiq hb]
  exact lintegral_congr fun ω => setLIntegral_Icc_nnnorm_sq_indicator_Ioc_mul H ha ω
include hℱ in
/-- **Itô isometry on a cell.** For `0 ≤ a < b`,
`𝔼‖∫_0^b H dW − ∫_0^a H dW‖² = 𝔼 ∫_{(a, b]} ‖H_s‖² ds`. -/
theorem lintegral_sq_stochasticIntegralBrownian_sub
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Ioc a b, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hb : (0 : ℝ) < b := lt_of_le_of_lt ha hab
  have hmF := measurable_uncurry_indicator_Ioc_mul H hm a b
  have hpF := progressivelyMeasurable_indicator_Ioc_mul ℱ H hp a b
  have hqF := lintegral_sq_indicator_Ioc_mul_lt_top (P := P) H hq a b
  have hloc := _root_.Prove2MeSourceProof.h_371bbffaec7b2a5d68568212 W ℱ hℱ H hm hp hq ha hab hmF hpF hqF hb
  rw [min_self, min_eq_left hab.le] at hloc
  have hcongr : ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s)
          hmF hpF hqF b ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hloc] with ω hω
    rw [hω]
  rw [hcongr]
  exact lintegral_sq_stochasticIntegralBrownian_indicator_Ioc W ℱ hℱ H ha hab hmF hpF hqF
end CellIsometry

end LevyStochCalc.Brownian.Ito


