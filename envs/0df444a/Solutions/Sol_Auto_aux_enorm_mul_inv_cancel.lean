-- Prove2me | solution 1 for Auto.aux_enorm_mul_inv_cancel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:58:07.842207+00:00
-- url     : https://prove2.me/submissions/f1f3071e-7ae5-435b-bf32-48fc1dec387b

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
theorem _root_.solution {z d : ℝ} (hz : 0 < z) :
    ENNReal.ofReal z⁻¹ * ‖z * d‖ₑ = ‖d‖ₑ := by
  rw [enorm_mul, Real.enorm_eq_ofReal hz.le, ENNReal.ofReal_inv_of_pos hz]
  rw [← mul_assoc, ENNReal.inv_mul_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr hz)) ENNReal.ofReal_ne_top, one_mul]
end Auto
