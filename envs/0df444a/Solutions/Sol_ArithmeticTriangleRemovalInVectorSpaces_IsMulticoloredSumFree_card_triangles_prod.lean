-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.card_triangles_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:52.71081+00:00
-- url     : https://prove2.me/submissions/1fabf236-699f-4367-a205-deb34219364a

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
variable [DecidableEq G] [DecidableEq W] [Fintype ι] [Fintype W]
namespace ArithmeticTriangleRemovalInVectorSpaces
namespace IsMulticoloredSumFree
theorem _root_.solution (h : IsMulticoloredSumFree x y z) :
    #(triangles (univ.image x ×ˢ (univ : Finset W)) (univ.image y ×ˢ univ) (univ.image z ×ˢ univ))
      = Fintype.card ι * Fintype.card W ^ 2 := by
  rw [sq, ← Fintype.card_prod, ← Fintype.card_prod, ← card_univ]
  symm
  refine card_bij (fun (i, a, b) _ ↦ ((x i, a), (y i, b), (z i, -(a + b)))) ?_ ?_ ?_
  · rintro ⟨i, a, b⟩ -
    simp only [mem_triangles, mem_product, mem_image, mem_univ, true_and, and_true, Prod.ext_iff,
      Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero]
    exact ⟨⟨i, rfl⟩, ⟨i, rfl⟩, ⟨i, rfl⟩, (h i i i).2 ⟨rfl, rfl⟩, by abel⟩
  · rintro ⟨i, a, b⟩ _ ⟨j, a', b'⟩ _ hst
    simp only [Prod.mk.injEq] at hst
    obtain ⟨⟨hx, rfl⟩, ⟨-, rfl⟩, -⟩ := hst
    rw [h.injective_left hx]
  · rintro ⟨⟨g₁, a⟩, ⟨g₂, b⟩, ⟨g₃, c⟩⟩ ht
    simp only [mem_triangles, mem_product, mem_image, mem_univ, true_and, and_true, Prod.ext_iff,
      Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at ht
    obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨k, rfl⟩, hsum, habc⟩ := ht
    obtain ⟨rfl, rfl⟩ := (h i j k).1 hsum
    refine ⟨(i, a, b), mem_univ _, ?_⟩
    simp only [Prod.mk.injEq, true_and]
    rw [eq_neg_of_add_eq_zero_right habc]
end IsMulticoloredSumFree
end ArithmeticTriangleRemovalInVectorSpaces
