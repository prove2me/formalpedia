-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.div_le_sq_div_mul_min_div_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:23.437152+00:00
-- url     : https://prove2.me/submissions/5a49c058-3405-4ae8-976f-4d0e3834585b

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mul_min_div_two_pos

set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution {c η X : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1) (hη : 0 < η)
    (hX : 1 ≤ X) : 6 / η ≤ (X / (c * min (1 - c) (c * η / 2) / 2)) ^ 2 := by
  have h := mul_min_div_two_pos hc₀ hc₁ hη
  have hη' : c * min (1 - c) (c * η / 2) / 2 ≤ η / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left (min_le_right (1 - c) (c * η / 2)) hc₀.le,
      mul_le_mul_of_nonneg_right (by nlinarith : c * c ≤ 1) hη.le]
  have h₈ : c * min (1 - c) (c * η / 2) / 2 ≤ 1 / 8 := by
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left (1 - c) (c * η / 2)) hc₀.le,
      sq_nonneg (c - 1 / 2)]
  rw [div_pow, div_le_div_iff₀ hη (pow_pos h 2)]
  nlinarith [mul_le_mul hη' h₈ h.le (by positivity), one_le_pow₀ (n := 2) hX]
end ArithmeticTriangleRemovalInVectorSpaces
