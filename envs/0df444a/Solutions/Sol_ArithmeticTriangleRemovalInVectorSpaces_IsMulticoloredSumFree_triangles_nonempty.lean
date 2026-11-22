-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.triangles_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:56.686369+00:00
-- url     : https://prove2.me/submissions/9e2896e3-7053-4b59-9355-0242b866d91f

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Abel
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Product
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_injective_left
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_injective_middle
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_injective_right
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_triangles
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_triangles


section
public section
open Finset Function
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {ι G W : Type*} [AddCommGroup G] [AddCommGroup W] {x y z : ι → G}
section Base
variable [DecidableEq G] [Fintype ι]
end Base
variable [DecidableEq G] [DecidableEq W] [Fintype ι] [Fintype W]
private lemma exists_add_add_eq_zero_of_card_compl_add_lt {A B C : Finset W}
    (h : #Aᶜ + #Bᶜ + #Cᶜ < Fintype.card W) : ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, a + b + c = 0 := by
  rw [card_compl, card_compl, card_compl] at h
  obtain ⟨c, hc⟩ : C.Nonempty := card_pos.1 (by grind [card_le_univ A, card_le_univ B])
  obtain ⟨a, ha⟩ : (A ∩ B.image fun b ↦ -c - b).Nonempty := by
    apply inter_nonempty_of_card_lt_card_add_card (subset_univ A) (subset_univ _)
    rw [card_image_of_injective _ sub_right_injective, card_univ]
    grind [card_le_univ A, card_le_univ B, card_le_univ C]
  obtain ⟨ha, hab⟩ := mem_inter.1 ha
  obtain ⟨b, hb, rfl⟩ := mem_image.1 hab
  exact ⟨_, ha, b, hb, c, hc, by abel⟩
omit [AddCommGroup G] [AddCommGroup W] in
/-- For injective `f`, the fibers of `(univ.image f ×ˢ univ) \ S` over the points `f i` have total
size at most `#((univ.image f ×ˢ univ) \ S)`. -/
private lemma sum_card_filter_notMem_le {f : ι → G} (hf : Injective f) (S : Finset (G × W)) :
    ∑ i, #{a | (f i, a) ∉ S} ≤ #((univ.image f ×ˢ univ) \ S) := by
  have hdisj : ((univ : Finset ι) : Set ι).PairwiseDisjoint
      fun i ↦ ({a | (f i, a) ∉ S} : Finset W).image (f i, ·) := by
    rintro i - j - hij
    simp only [Function.onFun, disjoint_left, mem_image]
    rintro _ ⟨a, -, rfl⟩ ⟨b, -, hb⟩
    obtain ⟨hji, -⟩ := Prod.mk.inj hb
    exact hij (hf hji.symm)
  have hsub : (univ.biUnion fun i ↦ ({a | (f i, a) ∉ S} : Finset W).image (f i, ·)) ⊆
      (univ.image f ×ˢ univ) \ S := by
    intro t ht
    simp only [mem_biUnion, mem_image, mem_filter, mem_univ, true_and] at ht
    obtain ⟨i, a, ha, rfl⟩ := ht
    simp [ha]
  grw [← card_le_card hsub, card_biUnion hdisj]
  simp [card_image_of_injective _ (Prod.mk_right_injective _)]
end ArithmeticTriangleRemovalInVectorSpaces
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open ArithmeticTriangleRemovalInVectorSpaces
variable {ι G W : Type*} [AddCommGroup G] [AddCommGroup W] {x y z : ι → G}
variable [DecidableEq G] [DecidableEq W] [Fintype ι] [Fintype W]
namespace ArithmeticTriangleRemovalInVectorSpaces
namespace IsMulticoloredSumFree
theorem _root_.solution (h : IsMulticoloredSumFree x y z)
    {X Y Z : Finset (G × W)}
    (hcard : #((univ.image x ×ˢ univ) \ X) + #((univ.image y ×ˢ univ) \ Y) +
      #((univ.image z ×ˢ univ) \ Z) < Fintype.card ι * Fintype.card W) :
    (triangles X Y Z).Nonempty := by
  obtain ⟨i, -, hi⟩ : ∃ i ∈ univ,
      #{a | (x i, a) ∉ X} + #{b | (y i, b) ∉ Y} + #{c | (z i, c) ∉ Z} < Fintype.card W := by
    apply exists_lt_of_sum_lt
    simp_rw [sum_add_distrib]
    grw [sum_card_filter_notMem_le h.injective_left X,
      sum_card_filter_notMem_le h.injective_middle Y, sum_card_filter_notMem_le h.injective_right Z]
    simpa using hcard
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ := exists_add_add_eq_zero_of_card_compl_add_lt
    (A := {a | (x i, a) ∈ X}) (B := {b | (y i, b) ∈ Y}) (C := {c | (z i, c) ∈ Z})
    (by simpa [compl_filter] using hi)
  simp only [mem_filter, mem_univ, true_and] at ha hb hc
  exact ⟨_, mem_triangles.2 ⟨ha, hb, hc, Prod.ext ((h i i i).2 ⟨rfl, rfl⟩) habc⟩⟩
end IsMulticoloredSumFree
end ArithmeticTriangleRemovalInVectorSpaces
