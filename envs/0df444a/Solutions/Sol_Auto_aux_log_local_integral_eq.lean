-- Prove2me | solution 1 for Auto.aux_log_local_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:56:39.89767+00:00
-- url     : https://prove2.me/submissions/44bc2937-837b-4296-9d26-b9b9ef80d1cd

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
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) (a : ℝ → ℝ) :
    (∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ ∂aux_logarithmicMeasure α β) =
      ∫⁻ t in Set.Icc x y, ‖deriv a t‖ₑ := by
  rw [aux_logarithmicMeasure]
  rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable]
  · rw [Measure.restrict_restrict_of_subset]
    · apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
      have htpos : 0 < t := lt_of_lt_of_le hα (hx.1.trans ht.1)
      simp only [Pi.mul_apply]
      rw [← ofReal_norm, norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
      rw [Real.norm_of_nonneg htpos.le, ENNReal.ofReal_inv_of_pos htpos]
      rw [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr htpos)
        ENNReal.ofReal_ne_top]
      simpa only [one_mul, Real.norm_eq_abs] using (ofReal_norm (deriv a t))
    · exact fun t ht => ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
  · exact ENNReal.measurable_ofReal.comp measurable_inv
  · exact measurableSet_Icc
  · filter_upwards with t
    exact ENNReal.ofReal_ne_top.lt_top
end Auto
