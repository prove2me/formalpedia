-- Prove2me | solution 1 for Auto.sequenceDistance_triangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:04:05.391799+00:00
-- url     : https://prove2.me/submissions/b3fca116-6be5-4def-9fb0-7a24619da0cb

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
public import Theorems.Thm_Auto_aux_sequenceDistance_le_of_within
public import Theorems.Thm_Auto_aux_withinSequenceDistance_trans

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution (a b c : ℤ → ℝ) :
    SequenceDistance a c ≤ SequenceDistance a b + SequenceDistance b c := by
  classical
  by_cases hab : ∃ k : ℕ, WithinSequenceDistance a b k
  · by_cases hbc : ∃ l : ℕ, WithinSequenceDistance b c l
    · have hcomp : WithinSequenceDistance a c (Nat.find hab + Nat.find hbc) :=
        aux_withinSequenceDistance_trans (Nat.find_spec hab) (Nat.find_spec hbc)
      rw [show SequenceDistance a b = (Nat.find hab : WithTop ℕ) by simp [SequenceDistance, hab],
        show SequenceDistance b c = (Nat.find hbc : WithTop ℕ) by simp [SequenceDistance, hbc]]
      calc
        SequenceDistance a c ≤ ((Nat.find hab + Nat.find hbc : ℕ) : WithTop ℕ) :=
          aux_sequenceDistance_le_of_within hcomp
        _ = (Nat.find hab : WithTop ℕ) + (Nat.find hbc : WithTop ℕ) := by simp
    · simp [SequenceDistance, hbc]
  · simp [SequenceDistance, hab]
end Auto
