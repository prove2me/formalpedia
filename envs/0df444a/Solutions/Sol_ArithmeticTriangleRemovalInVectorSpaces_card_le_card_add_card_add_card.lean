-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.card_le_card_add_card_add_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:53.648599+00:00
-- url     : https://prove2.me/submissions/22d248ff-e849-4b88-b5dc-d20accbdb67b

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_SliceRank_Diagonal
section
public section
open Finset Matrix Module
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {ι F : Type*} [Fintype ι] [Field F]
omit [Fintype ι] in
/-- A subspace `W` of `ι → F` with `#s < finrank F W` contains a nonzero vector that vanishes on
`s`. -/
private lemma exists_mem_ne_zero_forall_eq_zero_of_card_lt_finrank [Finite ι]
    (W : Submodule F (ι → F))
    {s : Finset ι} (hs : #s < finrank F W) : ∃ v ∈ W, v ≠ 0 ∧ ∀ i ∈ s, v i = 0 := by
  obtain ⟨⟨v, hvW⟩, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt
      (f := (LinearMap.funLeft F F ((↑) : s → ι)).comp W.subtype) (by simpa))
  refine ⟨v, hvW, by simpa using hv0, ?_⟩
  intro i hi
  simpa using congr_fun (LinearMap.mem_ker.1 hv) ⟨i, hi⟩
private lemma exists_mem_finrank_le_card [DecidableEq F] (W : Submodule F (ι → F)) :
    ∃ w ∈ W, finrank F W ≤ #{i | w i ≠ 0} := by
  classical
  obtain ⟨s, hs, hmax⟩ := exists_max_image
    ({s | ∃ w ∈ W, ({i | w i ≠ 0} : Finset ι) = s} : Finset (Finset ι)) card
    ⟨∅, by simpa using ⟨0, W.zero_mem, by simp⟩⟩
  obtain ⟨-, w, hw, rfl⟩ := mem_filter.1 hs
  refine ⟨w, hw, not_lt.1 ?_⟩
  intro hlt
  obtain ⟨v, hvW, hv0, hvs⟩ := exists_mem_ne_zero_forall_eq_zero_of_card_lt_finrank W hlt
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.1 hv0
  simp only [mem_filter, mem_univ, true_and] at hvs
  refine (hmax _ (mem_filter.2 ⟨mem_univ _, w + v, W.add_mem hw hvW, rfl⟩)).not_gt
    (card_lt_card ⟨?_, ?_⟩)
  · intro i hi
    simp_all
  · rw [not_subset]
    exact ⟨i₀, by simp [(by grind : w i₀ = 0), hi₀], by grind⟩
private lemma exists_forall_sum_mul_eq_zero_card_le [DecidableEq F] {α : Type*} (A : Finset α)
    (f : α → ι → F) :
    ∃ w : ι → F, (∀ a ∈ A, ∑ i, w i * f a i = 0) ∧ Fintype.card ι ≤ #A + #{i | w i ≠ 0} := by
  let L : Matrix A ι F := of fun a i ↦ f a i
  obtain ⟨w, hw, hcard⟩ := exists_mem_finrank_le_card (LinearMap.ker L.mulVecLin)
  refine ⟨w, ?_, ?_⟩
  · intro a ha
    simpa [L, mulVec, dotProduct, mul_comm] using congr_fun (LinearMap.mem_ker.1 hw) ⟨a, ha⟩
  · have := L.rank_le_card_height
    rw [Matrix.rank, Fintype.card_coe] at this
    grind [L.mulVecLin.finrank_range_add_finrank_ker, finrank_fintype_fun_eq_card]
private lemma card_filter_ne_zero_le_card_add_card [DecidableEq ι] [DecidableEq F] {α β γ : Type*}
    {A : Finset α} {B : Finset β} {C : Finset γ} (f : α → ι → F) (g : α → ι → ι → F)
    (f' : β → ι → F) (g' : β → ι → ι → F) (f'' : γ → ι → F) (g'' : γ → ι → ι → F)
    (h : ∀ i j k, (if i = j ∧ j = k then 1 else 0 : F) =
      ∑ a ∈ A, f a i * g a j k + ∑ b ∈ B, f' b j * g' b i k + ∑ c ∈ C, f'' c k * g'' c i j)
    {w : ι → F} (hw : ∀ a ∈ A, ∑ i, w i * f a i = 0) :
    #{i | w i ≠ 0} ≤ #B + #C := by
  let P : Matrix ι (B ⊕ C) F :=
    fun j x ↦ x.elim (fun b : B ↦ f' b j) fun c : C ↦ ∑ i, w i * g'' c i j
  let Q : Matrix (B ⊕ C) ι F :=
    fun x k ↦ x.elim (fun b : B ↦ ∑ i, w i * g' b i k) fun c : C ↦ f'' c k
  have hPQ : diagonal w = P * Q := by
    ext j k
    trans ∑ i, w i * (if i = j ∧ j = k then 1 else 0 : F)
    · by_cases hjk : j = k <;> simp [diagonal, hjk]
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [P, Q, Sum.elim_inl, Sum.elim_inr]
    rw [sum_coe_sort B fun b ↦ f' b j * ∑ i, w i * g' b i k,
      sum_coe_sort C fun c ↦ (∑ i, w i * g'' c i j) * f'' c k]
    simp_rw [h, mul_add, sum_add_distrib, mul_sum, sum_mul]
    rw [sum_comm, sum_eq_zero, zero_add, sum_comm, sum_comm (s := univ)]
    · congr 1 <;> congr with x <;> congr with i <;> ring
    · intro a ha
      simp_rw [← mul_assoc, ← sum_mul, hw a ha, zero_mul]
  rw [← Fintype.card_subtype, ← rank_diagonal, hPQ]
  grw [rank_mul_le_left, rank_le_card_width]
  simp
end ArithmeticTriangleRemovalInVectorSpaces
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Matrix Module
open ArithmeticTriangleRemovalInVectorSpaces
variable {ι F : Type*} [Fintype ι] [Field F]
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution [DecidableEq ι] {α β γ : Type*} {A : Finset α} {B : Finset β}
    {C : Finset γ} (f : α → ι → F) (g : α → ι → ι → F) (f' : β → ι → F) (g' : β → ι → ι → F)
    (f'' : γ → ι → F) (g'' : γ → ι → ι → F)
    (h : ∀ i j k, (if i = j ∧ j = k then 1 else 0 : F) =
      ∑ a ∈ A, f a i * g a j k + ∑ b ∈ B, f' b j * g' b i k + ∑ c ∈ C, f'' c k * g'' c i j) :
    Fintype.card ι ≤ #A + #B + #C := by
  classical
  obtain ⟨w, hw, hcard⟩ := exists_forall_sum_mul_eq_zero_card_le A f
  grw [hcard, card_filter_ne_zero_le_card_add_card f g f' g' f'' g'' h hw, add_assoc]
end ArithmeticTriangleRemovalInVectorSpaces
