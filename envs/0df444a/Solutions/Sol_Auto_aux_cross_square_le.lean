-- Prove2me | solution 1 for Auto.aux_cross_square_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:57:57.201355+00:00
-- url     : https://prove2.me/submissions/b829f209-4bb4-4bda-ba9f-4cf08b48dff7

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
theorem _root_.solution (u v : ℝ) :
    ‖u - v‖ₑ ^ (2 : ℕ) ≤
      2 * (‖u * u‖ₑ + ‖v * v‖ₑ) := by
  apply ENNReal.coe_le_coe.mpr
  exact (show ‖u - v‖₊ ^ (2 : ℕ) ≤
      2 * (‖u * u‖₊ + ‖v * v‖₊) by
    have hreal : |u - v| ^ 2 ≤ 2 * (|u * u| + |v * v|) := by
      rw [sq_abs, abs_of_nonneg (mul_self_nonneg u),
        abs_of_nonneg (mul_self_nonneg v)]
      nlinarith [sq_nonneg (u + v)]
    exact_mod_cast hreal)
end Auto
