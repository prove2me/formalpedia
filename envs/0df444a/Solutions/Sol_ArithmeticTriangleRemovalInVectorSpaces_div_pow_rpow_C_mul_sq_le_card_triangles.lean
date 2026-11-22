-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.div_pow_rpow_C_mul_sq_le_card_triangles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:22:32.48104+00:00
-- url     : https://prove2.me/submissions/e9e35702-9dff-4939-adf4-c66cf0cd0bd1

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_LowerBound
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_MaximalFamily
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_TensorPower
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Product
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_TensorPower
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_ZMod
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_div_rpow_C_mul_sq_le_card_triangles


set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open ArithmeticTriangleRemovalInVectorSpaces
variable {p n : ℕ} [Fact p.Prime]
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution {ι : Type*} [Fintype ι]
    {x y z : ι → Fin n → ZMod p} {X Y Z : Finset (Fin n → ZMod p)} (hx : Injective x)
    (hy : Injective y) (hz : Injective z) (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y)
    (hzZ : ∀ i, z i ∈ Z) (hsum : ∀ i, x i + y i + z i = 0) :
    (Fintype.card ι / (p : ℝ) ^ n) ^ C p * (p ^ n) ^ 2 ≤
      #((X ×ˢ Y ×ˢ Z).filter fun (u, v, w) ↦ u + v + w = 0) := by
  have := div_rpow_C_mul_sq_le_card_triangles (p := p) hx hy hz hxX hyY hzZ hsum
  rwa [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow] at this
end ArithmeticTriangleRemovalInVectorSpaces
