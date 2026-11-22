-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.card_le_rpow_one_sub_c_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:55.640813+00:00
-- url     : https://prove2.me/submissions/ff8efad9-2cc8-4e82-932a-3d905c1fd74b

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_LowerBound
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_MaximalFamily
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_TensorPower
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Product
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_TensorPower
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_ZMod
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_card_le_card_rpow


set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open ArithmeticTriangleRemovalInVectorSpaces
variable {p n : ℕ} [Fact p.Prime]
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution {ι : Type*} [Fintype ι] {x y z : ι → Fin n → ZMod p}
    (h : ∀ i j k, x i + y j + z k = 0 ↔ i = j ∧ j = k) :
    Fintype.card ι ≤ (p : ℝ) ^ ((1 - c p) * n) := by
  have := IsMulticoloredSumFree.card_le_card_rpow (p := p) h
  rwa [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm] at this
end ArithmeticTriangleRemovalInVectorSpaces
