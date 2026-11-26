-- Prove2me | solution 1 for Auto.sequenceDistance_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:04:03.152446+00:00
-- url     : https://prove2.me/submissions/69aacc67-aa9c-43b6-bf3b-96a6264ae37b

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
public import Theorems.Thm_Auto_aux_sequenceDistance_le_of_within
public import Theorems.Thm_Auto_aux_withinSequenceDistance_symm

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution (a b : ℤ → ℝ) :
    SequenceDistance a b = SequenceDistance b a := by
  classical
  by_cases h : ∃ k : ℕ, WithinSequenceDistance a b k
  · have h' : ∃ k : ℕ, WithinSequenceDistance b a k := by
      rcases h with ⟨k, hk⟩
      exact ⟨k, (aux_withinSequenceDistance_symm).1 hk⟩
    apply le_antisymm
    · rw [show SequenceDistance b a = (Nat.find h' : WithTop ℕ) by simp [SequenceDistance, h']]
      exact aux_sequenceDistance_le_of_within
        ((aux_withinSequenceDistance_symm).1 (Nat.find_spec h'))
    · rw [show SequenceDistance a b = (Nat.find h : WithTop ℕ) by simp [SequenceDistance, h]]
      exact aux_sequenceDistance_le_of_within
        ((aux_withinSequenceDistance_symm).2 (Nat.find_spec h))
  · have h' : ¬ ∃ k : ℕ, WithinSequenceDistance b a k := by
      intro hb
      rcases hb with ⟨k, hk⟩
      exact h ⟨k, (aux_withinSequenceDistance_symm).2 hk⟩
    simp [SequenceDistance, h, h']
end Auto
