-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.c_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:13.5402+00:00
-- url     : https://prove2.me/submissions/bdd89ccb-d258-469d-8c23-6cd476cfa54f

module
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_three_div_two_le_rpow_mul_sum
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_le_rpow_one_sub_c

set_option autoImplicit true
@[expose] public section
public section
open Finset Filter Topology
open ArithmeticTriangleRemovalInVectorSpaces
variable {p : ℕ}
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution (hp : 2 ≤ p) : c p < 1 := by
  by_contra! hc
  linarith [le_rpow_one_sub_c hp fun _ ↦ three_div_two_le_rpow_mul_sum hp,
    Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.2 (by grind) : (1 : ℝ) ≤ p)
      (by linarith : 1 - c p ≤ 0)]
end ArithmeticTriangleRemovalInVectorSpaces
