-- Prove2me | Definitions.Def_LevyStochCalc_Ito_CompensatedCellIsometry_F000
-- name    : LevyStochCalc_Ito_CompensatedCellIsometry_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:58:31.487903+00:00
-- url     : https://prove2.me/theorems/7a0f20fc-7866-4700-87cd-9152cc95e9a0
-- title:
--   LevyStochCalc source module: LevyStochCalc.Ito.CompensatedCellIsometry
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Ito.CompensatedCellIsometry in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F000
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F001
import Definitions.Def_SourceProof_e90edda898bb4b6c25399249

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô–Lévy isometry over a cell

The increment of the compensated Poisson integral across a time window `(a, b]` has second
moment the energy of the integrand over that window,

  `𝔼 |M_b - M_a|² = 𝔼 ∫_(a, b] ∫_E |φ(s, e)|² ν(de) ds`,

the window form of the horizon isometry `isometry_stochasticIntegral`.

## Main statements

* `lintegral_sq_indIoc_mul_Icc` — the energy over `[0, b]` of an integrand restricted to the
  window `(a, b]` is its energy over `(a, b]`.
* `isometry_stochasticIntegral_Ioc` — the Itô–Lévy isometry for the increment across `(a, b]`.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.2 (Thm 4.2.3).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

open LevyStochCalc.Brownian.Ito (indIoc)

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

section Energy

variable {ν : Measure E} {φ : Ω → ℝ → E → ℝ}

/-- The energy over the horizon `[0, b]` of a marked integrand restricted to the window
`(a, b]` is its energy over `(a, b]`. -/
theorem lintegral_sq_indIoc_mul_Icc {a b : ℝ} (ha : 0 ≤ a) (ω : Ω) :
    ∫⁻ s in Set.Icc (0 : ℝ) b, ∫⁻ e,
        (‖indIoc Ω a b ω s * φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume
      = ∫⁻ s in Set.Ioc a b, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume := by
  have hsub : Set.Ioc a b ⊆ Set.Icc (0 : ℝ) b := fun s hs => ⟨ha.trans hs.1.le, hs.2⟩
  have hpt : ∀ s : ℝ, ∫⁻ e, (‖indIoc Ω a b ω s * φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν
      = (Set.Ioc a b).indicator (fun s => ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) s := by
    intro s
    by_cases hs : s ∈ Set.Ioc a b
    · simp only [indIoc, Set.indicator_of_mem hs, one_mul]
    · simp [indIoc, Set.indicator_of_notMem hs]
  have hrw : ∫⁻ s in Set.Icc (0 : ℝ) b, ∫⁻ e,
        (‖indIoc Ω a b ω s * φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume
      = ∫⁻ s in Set.Icc (0 : ℝ) b,
          (Set.Ioc a b).indicator (fun s => ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) s ∂volume :=
    lintegral_congr hpt
  rw [hrw, setLIntegral_indicator measurableSet_Ioc, Set.inter_eq_left.mpr hsub]
end Energy

section Cell

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
  {φ : Ω → ℝ → E → ℝ}
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in
/-- **Itô–Lévy isometry over a cell.** The increment of the compensated integral across
`(a, b]` has second moment the energy of the integrand over `(a, b]`. -/
theorem isometry_stochasticIntegral_Ioc {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫⁻ ω, (‖stochasticIntegral N ℱ hℱ φ hm hp hq b ω
        - stochasticIntegral N ℱ hℱ φ hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Ioc a b, ∫⁻ e,
          (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  have hb : 0 < b := ha.trans_lt hab
  have hiso := isometry_stochasticIntegral N ℱ hℱ (fun ω s e => indIoc Ω a b ω s * φ ω s e)
    (measurable_indIoc_mul hm a b) (markedProgressivelyMeasurable_indIoc_mul hp a b)
    (sq_int_global_indIoc_mul hq a b) b hb
  have hL : ∫⁻ ω, (‖stochasticIntegral N ℱ hℱ (fun ω s e => indIoc Ω a b ω s * φ ω s e)
        (measurable_indIoc_mul hm a b) (markedProgressivelyMeasurable_indIoc_mul hp a b)
        (sq_int_global_indIoc_mul hq a b) b ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖stochasticIntegral N ℱ hℱ φ hm hp hq b ω
          - stochasticIntegral N ℱ hℱ φ hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [_root_.Prove2MeSourceProof.h_e90edda898bb4b6c25399249 N hℱ hm hp hq ha hab] with ω hω
    rw [hω]
  rw [← hL, hiso]
  exact lintegral_congr fun ω => lintegral_sq_indIoc_mul_Icc (φ := φ) (ν := ν) ha ω
end Cell

end LevyStochCalc.Poisson.Compensated


