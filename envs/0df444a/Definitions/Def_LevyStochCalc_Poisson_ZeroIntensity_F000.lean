-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_ZeroIntensity_F000
-- name    : LevyStochCalc_Poisson_ZeroIntensity_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:21:06.685193+00:00
-- url     : https://prove2.me/theorems/1fd7a0a4-a2c7-4d71-8fc2-badfd05e8714
-- title:
--   Source declarations: LevyStochCalc.Poisson.ZeroIntensity
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.ZeroIntensity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_RandomMeasure_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Regions of zero intensity carry no points

A region of zero reference intensity has a `Poisson(0)`-distributed count, and `Poisson(0)` is the
Dirac mass at `0`, so the count vanishes almost surely. In particular the reference intensity
`volume|_{[0, ∞)} ⊗ ν` gives no mass to negative times, so a Poisson random measure has no points
strictly before time `0`.

## Main statements

* `ae_count_eq_zero_of_intensity_eq_zero` — a zero-intensity region is empty almost surely.
* `ae_count_Iic_zero_eq_zero` — the counts on `B ∩ ((−∞, 0] × E)` vanish almost surely.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

theorem poissonMeasureENN_zero_ne_zero_eq_zero :
    poissonMeasureENN 0 {x : ℝ≥0∞ | x ≠ 0} = 0 := by
  have hms : MeasurableSet {x : ℝ≥0∞ | x ≠ 0} := (measurableSet_singleton (0 : ℝ≥0∞)).compl
  have hpre : ((↑) : ℕ → ℝ≥0∞) ⁻¹' {x : ℝ≥0∞ | x ≠ 0} = ({0} : Set ℕ)ᶜ := by
    ext n; simp
  rw [poissonMeasureENN, Measure.map_apply (by fun_prop) hms, hpre,
    prob_compl_eq_one_sub (measurableSet_singleton (0 : ℕ)), poissonMeasure_singleton]
  norm_num
/-- **A region of zero reference intensity carries no points almost surely.** -/
theorem ae_count_eq_zero_of_intensity_eq_zero (N : PoissonRandomMeasure.{u, v, w} P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) (h0 : referenceIntensity ν B = 0) :
    ∀ᵐ ω ∂P, N.N ω B = 0 := by
  have hlaw := N.poisson_law hB (by rw [h0]; exact ENNReal.zero_ne_top)
  rw [h0] at hlaw
  simp only [ENNReal.toNNReal_zero] at hlaw
  rw [ae_iff]
  have hset : {ω | ¬ N.N ω B = 0} = (fun ω => N.N ω B) ⁻¹' {x : ℝ≥0∞ | x ≠ 0} := rfl
  have hms : MeasurableSet {x : ℝ≥0∞ | x ≠ 0} := (measurableSet_singleton (0 : ℝ≥0∞)).compl
  rw [hset, ← Measure.map_apply (N.measurable_eval hB) hms, hlaw]
  exact poissonMeasureENN_zero_ne_zero_eq_zero
/-- The reference intensity gives no mass to the times at or before `0`. -/
theorem referenceIntensity_inter_Iic_zero (B : Set (ℝ × E)) :
    referenceIntensity ν (B ∩ Set.Iic (0 : ℝ) ×ˢ Set.univ) = 0 := by
  refine measure_mono_null Set.inter_subset_right ?_
  rw [referenceIntensity, Measure.prod_prod, Measure.restrict_apply measurableSet_Iic]
  have : Set.Iic (0 : ℝ) ∩ Set.Ici (0 : ℝ) = {(0 : ℝ)} := by
    ext x; simp [Set.mem_Iic, Set.mem_Ici, le_antisymm_iff]
  rw [this, Real.volume_singleton, zero_mul]
/-- **A Poisson random measure has no points at or before time `0`.** -/
theorem ae_count_Iic_zero_eq_zero (N : PoissonRandomMeasure.{u, v, w} P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) :
    ∀ᵐ ω ∂P, N.N ω (B ∩ Set.Iic (0 : ℝ) ×ˢ Set.univ) = 0 :=
  ae_count_eq_zero_of_intensity_eq_zero N
    (hB.inter (measurableSet_Iic.prod MeasurableSet.univ))
    (referenceIntensity_inter_Iic_zero B)
end LevyStochCalc.Poisson


