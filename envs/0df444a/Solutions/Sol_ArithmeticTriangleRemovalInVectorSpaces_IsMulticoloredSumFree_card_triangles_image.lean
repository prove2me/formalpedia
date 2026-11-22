-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.card_triangles_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:58.936269+00:00
-- url     : https://prove2.me/submissions/bdc29bd6-8134-4859-a5a9-75662ff873e4

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Abel
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Product
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_injective_left
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_triangles
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_triangles



set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open ArithmeticTriangleRemovalInVectorSpaces
variable {ι G W : Type*} [AddCommGroup G] [AddCommGroup W] {x y z : ι → G}
variable [DecidableEq G] [Fintype ι]
namespace ArithmeticTriangleRemovalInVectorSpaces
namespace IsMulticoloredSumFree
theorem _root_.solution (h : IsMulticoloredSumFree x y z) :
    #(triangles (univ.image x) (univ.image y) (univ.image z)) = Fintype.card ι := by
  rw [← card_univ]
  symm
  refine card_bij (fun i _ ↦ (x i, y i, z i)) ?_ ?_ ?_
  · intro i _
    simpa using (h i i i).2 ⟨rfl, rfl⟩
  · intro i _ j _ hij
    obtain ⟨hx, -⟩ := Prod.mk.inj hij
    exact h.injective_left hx
  · rintro ⟨g₁, g₂, g₃⟩ ht
    simp only [mem_triangles, mem_image, mem_univ, true_and] at ht
    obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨k, rfl⟩, hsum⟩ := ht
    obtain ⟨rfl, rfl⟩ := (h i j k).1 hsum
    exact ⟨i, mem_univ _, rfl⟩
end IsMulticoloredSumFree
end ArithmeticTriangleRemovalInVectorSpaces
