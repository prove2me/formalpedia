-- Prove2me | solution 1 for Auto.sequenceDistance_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:04:33.334598+00:00
-- url     : https://prove2.me/submissions/4e2210ce-570d-4bfb-b40d-301a24f3ffeb

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
public import Theorems.Thm_Auto_aux_sequenceDistance_le_of_within

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution (a b : ℤ → ℝ) {t : ℝ} (ht : 0 < t) :
    SequenceDistance (fun j => t * a j) (fun j => t * b j) = SequenceDistance a b := by
  classical
  have hiff (k : ℕ) :
      WithinSequenceDistance (fun j => t * a j) (fun j => t * b j) k ↔
        WithinSequenceDistance a b k := by
    constructor <;> intro h <;> intro j
    · constructor
      · nlinarith [(h j).1]
      · nlinarith [(h j).2]
    · constructor
      · exact mul_le_mul_of_nonneg_left (h j).1 (le_of_lt ht)
      · exact mul_le_mul_of_nonneg_left (h j).2 (le_of_lt ht)
  by_cases h : ∃ k : ℕ, WithinSequenceDistance a b k
  · have h' : ∃ k : ℕ, WithinSequenceDistance (fun j => t * a j) (fun j => t * b j) k := by
      rcases h with ⟨k, hk⟩
      exact ⟨k, (hiff k).2 hk⟩
    apply le_antisymm
    · rw [show SequenceDistance a b = (Nat.find h : WithTop ℕ) by simp [SequenceDistance, h]]
      exact aux_sequenceDistance_le_of_within ((hiff (Nat.find h)).2 (Nat.find_spec h))
    · rw [show SequenceDistance (fun j => t * a j) (fun j => t * b j) =
        (Nat.find h' : WithTop ℕ) by simp [SequenceDistance, h']]
      exact aux_sequenceDistance_le_of_within ((hiff (Nat.find h')).1 (Nat.find_spec h'))
  · have h' : ¬ ∃ k : ℕ, WithinSequenceDistance (fun j => t * a j) (fun j => t * b j) k := by
      intro h'
      rcases h' with ⟨k, hk⟩
      exact h ⟨k, (hiff k).1 hk⟩
    simp [SequenceDistance, h, h']
end Auto
