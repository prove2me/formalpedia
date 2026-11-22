-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.triangles_nonempty_of_card_sdiff_add_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:00.805306+00:00
-- url     : https://prove2.me/submissions/b8f08e19-02b3-4e08-bdee-9181683ad446

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Abel
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Product
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
theorem _root_.solution (hx : Injective x) (hy : Injective y)
    (hz : Injective z) (hsum : ∀ i, x i + y i + z i = 0) {X Y Z : Finset G}
    (hcard : #(univ.image x \ X) + #(univ.image y \ Y) + #(univ.image z \ Z) < Fintype.card ι) :
    (triangles X Y Z).Nonempty := by
  classical
  have hle (f : ι → G) (hf : Injective f) (S : Finset G) :
      #({i | f i ∉ S} : Finset ι) ≤ #(univ.image f \ S) := by
    apply card_le_card_of_injOn f _ hf.injOn
    intro i hi
    simp_all
  obtain ⟨i, -, hi⟩ : ∃ i ∈ univ, i ∉ (univ.filter fun i ↦ x i ∉ X) ∪
      (univ.filter fun i ↦ y i ∉ Y) ∪ univ.filter fun i ↦ z i ∉ Z := by
    apply exists_mem_notMem_of_card_lt_card
    grw [card_union_le, card_union_le, hle x hx X, hle y hy Y, hle z hz Z, card_univ]
    exact hcard
  simp only [mem_union, mem_filter, mem_univ, true_and, not_or, not_not] at hi
  obtain ⟨⟨hxi, hyi⟩, hzi⟩ := hi
  exact ⟨_, mem_triangles.2 ⟨hxi, hyi, hzi, hsum i⟩⟩
end ArithmeticTriangleRemovalInVectorSpaces
