-- Prove2me | solution 1 for Auto.aux_log_measure_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:56:40.465738+00:00
-- url     : https://prove2.me/submissions/5857689c-5441-47be-a7f5-6c6f9542955f

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {α β x y : ℝ} (hα : 0 < α)
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) :
    aux_logarithmicMeasure α β (Set.Icc x y) ≤ ENNReal.ofReal ((β - α) / α) := by
  rw [aux_logarithmicMeasure, withDensity_apply _ measurableSet_Icc]
  rw [Measure.restrict_restrict_of_subset (Icc_subset_Icc hx.1 hy.2)]
  calc
    ∫⁻ a in Set.Icc x y, ENNReal.ofReal a⁻¹ ∂volume ≤
        ∫⁻ _a in Set.Icc x y, ENNReal.ofReal α⁻¹ ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
      gcongr
      exact hx.1.trans ht.1
    _ = ENNReal.ofReal α⁻¹ * ENNReal.ofReal (y - x) := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
    _ ≤ ENNReal.ofReal α⁻¹ * ENNReal.ofReal (β - α) := by
      gcongr
      all_goals linarith [hx.1, hy.2]
    _ = ENNReal.ofReal ((β - α) / α) := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hα.le)]
      field_simp
end Auto
