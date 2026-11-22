-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.mul_min_div_two_lt_inv_max_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:22.883657+00:00
-- url     : https://prove2.me/submissions/0895efd9-0058-48ce-baa4-ae7381fe71e4

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mul_min_div_two_pos
section
public section
namespace ArithmeticTriangleRemovalInVectorSpaces
private lemma mul_one_sub_mul_le_inv_sub {c κ : ℝ} (hκ : 0 < κ) : c * (1 - c * κ) ≤ κ⁻¹ - c := by
  rw [le_sub_iff_add_le, ← mul_one κ⁻¹, le_inv_mul_iff₀ hκ]
  nlinarith [sq_nonneg (1 - c * κ)]
end ArithmeticTriangleRemovalInVectorSpaces
end
end

set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution {c η : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1) (hη : 0 < η) :
    c * min (1 - c) (c * η / 2) / 2 < (max 1 (c⁻¹ - η / 2))⁻¹ - c := by
  have hmin : min (1 - c) (c * η / 2) ≤ 1 - c * max 1 (c⁻¹ - η / 2) := by
    rcases le_total 1 (c⁻¹ - η / 2) with h | h
    · rw [max_eq_right h, mul_sub, mul_inv_cancel₀ hc₀.ne']
      linarith [min_le_right (1 - c) (c * η / 2)]
    · rw [max_eq_left h, mul_one]
      exact min_le_left _ _
  grw [← mul_one_sub_mul_le_inv_sub (lt_max_of_lt_left one_pos)]
  linarith [mul_le_mul_of_nonneg_left hmin hc₀.le, mul_min_div_two_pos hc₀ hc₁ hη]
end ArithmeticTriangleRemovalInVectorSpaces
