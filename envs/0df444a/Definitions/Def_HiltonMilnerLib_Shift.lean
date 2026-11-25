-- Prove2me | Definitions.Def_HiltonMilnerLib_Shift
-- name    : HiltonMilnerLib_Shift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:44:23.491154+00:00
-- url     : https://prove2.me/theorems/48de13b0-7240-441c-91df-69f4b128e75c
-- title:
--   Shift
-- statement:
--   Definitions and structural lemmas for Shift, from Juan Pablo Traverso Gianini (jtraverso/hilton-milner; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Hilton-Milner theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/Shift.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace HiltonMilner
def Cross (𝒜 ℬ : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ 𝒜, ∀ B ∈ ℬ, (A ∩ B).Nonempty
lemma Cross.symm {𝒜 ℬ : Finset (Finset ℕ)} (h : Cross 𝒜 ℬ) : Cross ℬ 𝒜 :=
  fun B hB A hA => by rw [inter_comm]; exact h A hA B hB
def wt (A : Finset ℕ) : ℕ := ∑ x ∈ A, x
def fwt (𝒜 : Finset (Finset ℕ)) : ℕ := ∑ A ∈ 𝒜, wt A
def shiftSet (y z : ℕ) (A : Finset ℕ) : Finset ℕ :=
  if y ∉ A ∧ z ∈ A then insert y (A.erase z) else A
abbrev sh (y z : ℕ) (𝒜 : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  UV.compression ({y} : Finset ℕ) {z} 𝒜
lemma compress_eq (y z : ℕ) (A : Finset ℕ) :
    UV.compress ({y} : Finset ℕ) {z} A = shiftSet y z A := by
  unfold UV.compress shiftSet
  by_cases h : y ∉ A ∧ z ∈ A
  · have hyz : y ≠ z := fun e => h.1 (e ▸ h.2)
    rw [if_pos ⟨Finset.disjoint_singleton_left.2 h.1, Finset.singleton_subset_iff.2 h.2⟩,
      if_pos h]
    ext x
    simp only [Finset.sup_eq_union, mem_sdiff, mem_union, mem_singleton, mem_insert, mem_erase]
    constructor
    · rintro ⟨hx | hx, hxz⟩
      · exact Or.inr ⟨hxz, hx⟩
      · exact Or.inl hx
    · rintro (hx | ⟨hxz, hx⟩)
      · exact ⟨Or.inr hx, hx ▸ hyz⟩
      · exact ⟨Or.inl hx, hxz⟩
  · rw [if_neg, if_neg h]
    rintro ⟨h1, h2⟩
    exact h ⟨Finset.disjoint_singleton_left.1 h1, Finset.singleton_subset_iff.1 h2⟩
lemma mem_sh {y z : ℕ} {𝒜 : Finset (Finset ℕ)} {A : Finset ℕ} :
    A ∈ sh y z 𝒜 ↔ (A ∈ 𝒜 ∧ shiftSet y z A ∈ 𝒜) ∨
      (A ∉ 𝒜 ∧ ∃ B ∈ 𝒜, y ∉ B ∧ z ∈ B ∧ A = insert y (B.erase z)) := by
  rw [UV.mem_compression]
  simp only [compress_eq]
  constructor
  · rintro (h | ⟨hA, B, hB, hBA⟩)
    · exact Or.inl h
    · refine Or.inr ⟨hA, B, hB, ?_⟩
      unfold shiftSet at hBA
      split_ifs at hBA with hc
      · exact ⟨hc.1, hc.2, hBA.symm⟩
      · exact absurd (hBA ▸ hB) hA
  · rintro (h | ⟨hA, B, hB, hy, hz, rfl⟩)
    · exact Or.inl h
    · refine Or.inr ⟨hA, B, hB, ?_⟩
      unfold shiftSet; rw [if_pos ⟨hy, hz⟩]
lemma cross_keep_move {y z : ℕ} {𝒜 ℬ : Finset (Finset ℕ)} (h : Cross 𝒜 ℬ) {A B : Finset ℕ}
    (hA : A ∈ 𝒜) (hA' : shiftSet y z A ∈ 𝒜) (hB : B ∈ ℬ) (hyB : y ∉ B) (hzB : z ∈ B) :
    (A ∩ insert y (B.erase z)).Nonempty := by
  obtain ⟨w, hw⟩ := h A hA B hB
  rw [mem_inter] at hw
  by_cases hwz : w = z
  · subst hwz
    by_cases hyA : y ∈ A
    · exact ⟨y, mem_inter.2 ⟨hyA, mem_insert_self _ _⟩⟩
    · have hsA : shiftSet y w A = insert y (A.erase w) := by
        unfold shiftSet; rw [if_pos ⟨hyA, hw.1⟩]
      rw [hsA] at hA'
      obtain ⟨u, hu⟩ := h _ hA' B hB
      rw [mem_inter, mem_insert, mem_erase] at hu
      rcases hu.1 with rfl | ⟨huw, huA⟩
      · exact absurd hu.2 hyB
      · exact ⟨u, mem_inter.2 ⟨huA, mem_insert_of_mem (mem_erase.2 ⟨huw, hu.2⟩)⟩⟩
  · exact ⟨w, mem_inter.2 ⟨hw.1, mem_insert_of_mem (mem_erase.2 ⟨hwz, hw.2⟩)⟩⟩
lemma Cross.sh {y z : ℕ} {𝒜 ℬ : Finset (Finset ℕ)} (h : Cross 𝒜 ℬ) :
    Cross (sh y z 𝒜) (sh y z ℬ) := by
  intro A hA B hB
  rcases mem_sh.1 hA with ⟨hA, hA'⟩ | ⟨-, A₀, hA₀, hyA, hzA, rfl⟩ <;>
    rcases mem_sh.1 hB with ⟨hB, hB'⟩ | ⟨-, B₀, hB₀, hyB, hzB, rfl⟩
  · exact h A hA B hB
  · exact cross_keep_move h hA hA' hB₀ hyB hzB
  · rw [inter_comm]; exact cross_keep_move h.symm hB hB' hA₀ hyA hzA
  · exact ⟨y, mem_inter.2 ⟨mem_insert_self _ _, mem_insert_self _ _⟩⟩
end HiltonMilner


