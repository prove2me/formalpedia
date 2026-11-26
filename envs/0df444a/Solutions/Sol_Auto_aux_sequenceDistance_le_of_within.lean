-- Prove2me | solution 1 for Auto.aux_sequenceDistance_le_of_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:38:34.577723+00:00
-- url     : https://prove2.me/submissions/d2a983d0-c856-4f8d-8e63-86f6b46896c1

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution {a b : ℤ → ℝ} {k : ℕ}
    (hk : WithinSequenceDistance a b k) : SequenceDistance a b ≤ (k : WithTop ℕ) := by
  classical
  by_cases h : ∃ l : ℕ, WithinSequenceDistance a b l
  · simp only [SequenceDistance, dif_pos h]
    exact_mod_cast Nat.find_min' h hk
  · exact (h ⟨k, hk⟩).elim
end Auto
