-- Prove2me | solution 1 for AppliedComb.Posets.dual_dilworth
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T15:37:12.509461+00:00
-- url     : https://prove2.me/submissions/3ba382a6-5e5d-4fa9-9a11-98f677b7d954

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_AppliedComb_Posets_chainPartition

set_option autoImplicit false

namespace P193f7294

open AppliedComb.Posets

open Classical in
/-- Largest size of a chain all of whose elements lie below `x`. -/
noncomputable def lev {α : Type*} [PartialOrder α] [Fintype α] (x : α) : ℕ :=
  ((Finset.univ : Finset (Finset α)).filter
    (fun C : Finset α => IsChain (· ≤ ·) (C : Set α) ∧ ∀ y ∈ C, y ≤ x)).sup Finset.card

theorem lev_le_height {α : Type*} [PartialOrder α] [Fintype α] (x : α) :
    lev x ≤ height α := by
  classical
  unfold lev height
  apply Finset.sup_le
  intro C hC
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
  have hm : C ∈ (Finset.univ : Finset (Finset α)).filter
      (fun C : Finset α => IsChain (· ≤ ·) (C : Set α)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hC.1
  exact Finset.le_sup (f := Finset.card) hm

theorem one_le_lev {α : Type*} [PartialOrder α] [Fintype α] (x : α) : 1 ≤ lev x := by
  classical
  unfold lev
  have hmem : ({x} : Finset α) ∈ (Finset.univ : Finset (Finset α)).filter
      (fun C : Finset α => IsChain (· ≤ ·) (C : Set α) ∧ ∀ y ∈ C, y ≤ x) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_singleton]
    refine ⟨Set.Subsingleton.isChain Set.subsingleton_singleton, ?_⟩
    intro y hy
    rw [Finset.mem_singleton] at hy
    rw [hy]
  have := Finset.le_sup (f := Finset.card) hmem
  simpa using this

theorem lev_lt {α : Type*} [PartialOrder α] [Fintype α] {x y : α} (hxy : x < y) :
    lev x < lev y := by
  classical
  have hne : ((Finset.univ : Finset (Finset α)).filter
      (fun C : Finset α => IsChain (· ≤ ·) (C : Set α) ∧ ∀ z ∈ C, z ≤ x)).Nonempty :=
    ⟨∅, by simp⟩
  obtain ⟨C, hC, hCeq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
  have hyC : y ∉ C := fun h => absurd (hC.2 y h) (not_le_of_gt hxy)
  have hmem : insert y C ∈ (Finset.univ : Finset (Finset α)).filter
      (fun C : Finset α => IsChain (· ≤ ·) (C : Set α) ∧ ∀ z ∈ C, z ≤ y) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_insert]
    refine ⟨hC.1.insert ?_, ?_⟩
    · intro b hb _
      exact Or.inr ((hC.2 b hb).trans hxy.le)
    · intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact le_rfl
      · exact (hC.2 z hz).trans hxy.le
  have h1 := Finset.le_sup (f := Finset.card) hmem
  rw [Finset.card_insert_of_notMem hyC] at h1
  have h2 : lev x = C.card := hCeq
  have h3 : lev y = ((Finset.univ : Finset (Finset α)).filter
      (fun C : Finset α => IsChain (· ≤ ·) (C : Set α) ∧ ∀ z ∈ C, z ≤ y)).sup Finset.card := rfl
  omega

end P193f7294

open AppliedComb.Posets in
theorem solution (α : Type*) [PartialOrder α] [Fintype α] :
    (∃ A : Fin (height α) → Finset α, IsAntichainPartition A) ∧
    ∀ (k : ℕ) (A : Fin k → Finset α), IsAntichainPartition A → height α ≤ k := by
  classical
  refine ⟨?_, ?_⟩
  · refine ⟨fun i => Finset.univ.filter (fun x => P193f7294.lev x = i.val + 1), ?_, ?_, ?_⟩
    · intro i x hx y hy hxy hle
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      have := P193f7294.lev_lt (lt_of_le_of_ne hle hxy)
      omega
    · intro i j hij
      rw [Finset.disjoint_left]
      intro x hx hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact hij (Fin.ext (by omega))
    · intro x
      have h1 := P193f7294.one_le_lev x
      have h2 := P193f7294.lev_le_height x
      refine ⟨⟨P193f7294.lev x - 1, by omega⟩, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
  · intro k A hA
    obtain ⟨hanti, _, hcov⟩ := hA
    unfold height
    apply Finset.sup_le
    intro C hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
    have hk : (Finset.univ : Finset (Fin k)).card = k := by simp
    rw [← hk]
    refine Finset.card_le_card_of_injOn (fun x => Classical.choose (hcov x)) ?_ ?_
    · intro a _
      simp
    · intro a ha b hb hab
      by_contra hne
      have hA' := Classical.choose_spec (hcov a)
      have hB' := Classical.choose_spec (hcov b)
      simp only at hab
      rw [hab] at hA'
      rcases hC ha hb hne with h | h
      · exact hanti _ hA' hB' hne h
      · exact hanti _ hB' hA' (Ne.symm hne) h
