-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.inv_pow_le_inv_add_sq_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:22.317805+00:00
-- url     : https://prove2.me/submissions/058918b7-d8b4-41e6-bb96-711d1db9e39a

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent

set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution {P η : ℝ} (hP : 2 ≤ P) (hη : 0 < η) {n : ℕ} (hn : 6 / η ≤ n) :
    (P ^ n)⁻¹ ≤ (P + P ^ 2)⁻¹ ^ (2 / η) := by
  rw [Real.inv_rpow (by positivity)]
  gcongr
  grw [(by nlinarith : P + P ^ 2 ≤ P ^ 3), ← Real.rpow_natCast_mul (by positivity),
    ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith)
    (by push_cast; linarith [(by ring : 3 * (2 / η) = 6 / η)])
end ArithmeticTriangleRemovalInVectorSpaces
