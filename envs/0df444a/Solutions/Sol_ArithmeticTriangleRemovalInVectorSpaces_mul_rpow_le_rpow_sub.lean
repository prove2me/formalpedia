-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.mul_rpow_le_rpow_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:21.841861+00:00
-- url     : https://prove2.me/submissions/e30f998c-3b96-49c3-a575-0416b4266d43

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent

set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution {A ε κ C η : ℝ} (hA : 0 < A) (hε0 : 0 < ε) (hε₁ : ε ≤ 1) (hη : 0 < η)
    (hκ : C - η / 2 ≤ 1 + κ) (hε : ε ≤ A⁻¹ ^ (2 / η)) : A * ε ^ (1 + κ) ≤ ε ^ (C - η) := by
  have hεη : ε ^ (η / 2) ≤ A⁻¹ := by
    grw [hε, ← Real.rpow_mul (by positivity), div_mul_div_cancel₀ (by positivity),
      div_self two_ne_zero, Real.rpow_one]
  calc A * ε ^ (1 + κ) ≤ A * ε ^ (C - η / 2) := by
        grw [Real.rpow_le_rpow_of_exponent_ge hε0 hε₁ hκ]
    _ = A * ε ^ (η / 2) * ε ^ (C - η) := by
        rw [mul_assoc, ← Real.rpow_add hε0]
        ring_nf
    _ ≤ ε ^ (C - η) := by
        grw [hεη, mul_inv_cancel₀ hA.ne', one_mul]
end ArithmeticTriangleRemovalInVectorSpaces
