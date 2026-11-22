-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.inv_pow_le_mul_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:15.714804+00:00
-- url     : https://prove2.me/submissions/7e4e60b0-64c0-49d0-b864-d3fd3d8301f7

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent

set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution {P ε κ : ℝ} {n : ℕ} (hP : 0 < P) (hε : 0 < ε) (hκ : 0 < κ)
    (h : ε⁻¹ < (P ^ κ⁻¹) ^ (n + 1)) : (P ^ n)⁻¹ ≤ P * ε ^ κ := by
  have := Real.rpow_lt_rpow (by positivity) h hκ
  rw [← Real.rpow_mul_natCast hP.le, ← Real.rpow_mul hP.le, mul_right_comm,
    inv_mul_cancel₀ hκ.ne', one_mul, Real.rpow_natCast, Real.inv_rpow hε.le,
    inv_lt_iff_one_lt_mul₀ (by positivity), pow_succ'] at this
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  linarith
end ArithmeticTriangleRemovalInVectorSpaces
