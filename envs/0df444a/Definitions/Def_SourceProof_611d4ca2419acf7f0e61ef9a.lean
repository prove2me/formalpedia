-- Prove2me | Definitions.Def_SourceProof_611d4ca2419acf7f0e61ef9a
-- name    : SourceProof_611d4ca2419acf7f0e61ef9a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:25:30.045666+00:00
-- url     : https://prove2.me/theorems/7d61d6b7-9394-477d-b7c6-c98a9099ae1e
-- title:
--   LevyStochCalc source module: SourceProof_611d4ca2419acf7f0e61ef9a
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_sq_sub_le` comes from the `LevyStochCalc.Brownian.ItoProcessVersion` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoProcessVersion_F000
import Definitions.Def_SourceProof_00809733168215a41b1415ee

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Continuous adapted versions of an Itô process

The Itô integral is defined time by time, so the process `t ↦ X_t` it produces has no path
regularity built in. `IsItoVersion` names a continuous adapted process agreeing with the Itô
process at each time; such a version has jointly measurable paths, so it can be composed with a
continuous function and fed back into a time integral or an Itô integral.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsItoVersion` — a continuous adapted version of an Itô process.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.measurable_uncurry` — its joint measurability.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.progressivelyMeasurable_comp` — a continuous function
  of it is progressively measurable.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.sub_ae` — its increment splits into drift and
  martingale parts.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sub_le` and
  `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_sq_sub_le` — the increment moments carried
  over from `itoProcess`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Version

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

variable {W ℱ hℱ H hm hp hq} {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}

section Moments

variable {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_611d4ca2419acf7f0e61ef9a (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    MeasureTheory.Integrable (fun ω : Ω => (X v ω - X u ω) ^ 2) P
      ∧ ∫ ω, (X v ω - X u ω) ^ 2 ∂P ≤ 2 * (B * (v - u)) ^ 2 + 2 * (C ^ 2 * (v - u)) := by
  rcases eq_or_lt_of_le huv with rfl | hlt
  · refine ⟨by simp, ?_⟩
    simp
  · obtain ⟨hint, hle⟩ := _root_.Prove2MeSourceProof.h_00809733168215a41b1415ee W ℱ hℱ H hm hp hq hC0 hCH X₀ bdrift
      hbm hB0 hB hu hlt
    have hae : (fun ω : Ω => (X v ω - X u ω) ^ 2)
        =ᵐ[P] fun ω => (LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift v ω
          - LevyStochCalc.Brownian.Ito.itoProcess W ℱ hℱ H hm hp hq X₀ bdrift u ω) ^ 2 := by
      filter_upwards [h.ae_eq v (hu.trans huv), h.ae_eq u hu] with ω hv hu'
      rw [hv, hu']
    exact ⟨hint.congr hae.symm, by rw [MeasureTheory.integral_congr_ae hae]; exact hle⟩
end Moments

end Version

end LevyStochCalc.Brownian.Ito


