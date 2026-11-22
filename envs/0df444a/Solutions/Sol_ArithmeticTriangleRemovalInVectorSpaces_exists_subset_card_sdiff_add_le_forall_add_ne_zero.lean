-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.exists_subset_card_sdiff_add_le_forall_add_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:23:37.675693+00:00
-- url     : https://prove2.me/submissions/adf14575-6acf-4c5a-802a-9752ed431624

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_LowerBound
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_MaximalFamily
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_TensorPower
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Product
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_TensorPower
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_ZMod
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_exists_subset_card_sdiff_add_le_of_card_triangles_lt
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_sumTriples
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_triangles
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mk_mem_vecSumTriples
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_shares_mk
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_triangles_eq_empty_iff
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_typeClass_nonempty
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_sumTriples
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_triangles
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mk_mem_vecSumTriples
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.shares_mk
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.typeClass_nonempty



set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open ArithmeticTriangleRemovalInVectorSpaces
variable {p n : ℕ} [Fact p.Prime]
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution {ε : ℝ} (hε : 0 ≤ ε)
    {X Y Z : Finset (Fin n → ZMod p)}
    (h : #((X ×ˢ Y ×ˢ Z).filter fun (x, y, z) ↦ x + y + z = 0) < (ε / 3) ^ C p * (p ^ n) ^ 2) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z, #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * p ^ n ∧
      ∀ x ∈ X', ∀ y ∈ Y', ∀ z ∈ Z', x + y + z ≠ 0 := by
  have hN : (Fintype.card (Fin n → ZMod p) : ℝ) = p ^ n := by simp
  obtain ⟨X', hX', Y', hY', Z', hZ', hcard, hempty⟩ :=
    exists_subset_card_sdiff_add_le_of_card_triangles_lt (X := X) (Y := Y) (Z := Z) hε
      (by rwa [hN])
  exact ⟨X', hX', Y', hY', Z', hZ', by rwa [← hN], triangles_eq_empty_iff.1 hempty⟩
end ArithmeticTriangleRemovalInVectorSpaces
