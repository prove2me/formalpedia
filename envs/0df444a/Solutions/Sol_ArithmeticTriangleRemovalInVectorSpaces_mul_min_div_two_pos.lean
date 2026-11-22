-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.mul_min_div_two_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:59.420426+00:00
-- url     : https://prove2.me/submissions/ed2f0908-c317-4aef-9a41-28b7869bded7

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent

set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution {c η : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1) (hη : 0 < η) :
    0 < c * min (1 - c) (c * η / 2) / 2 := by
  have := lt_min (sub_pos.2 hc₁) (by positivity : 0 < c * η / 2)
  positivity
end ArithmeticTriangleRemovalInVectorSpaces
