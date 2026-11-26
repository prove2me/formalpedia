-- Prove2me | solution 1 for Auto.sequenceDistance_shift_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:04:07.606518+00:00
-- url     : https://prove2.me/submissions/d53377c7-9eb0-4225-9050-c86a2c4df74e

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
public import Theorems.Thm_Auto_aux_spacedSequence_le_succ
public import Theorems.Thm_Auto_aux_spacedSequence_monotone
public import Theorems.Thm_Auto_aux_sequenceDistance_le_of_within

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution {a b c : ℤ → ℝ}
    (ha : SpacedSequence a) (hb : SpacedSequence b)
    (hc : ∀ j : ℤ, c j = b (j + 1)) :
    SequenceDistance a c ≤ SequenceDistance a b + 1 := by
  classical
  by_cases hab : ∃ k : ℕ, WithinSequenceDistance a b k
  · have hwithin : WithinSequenceDistance a c (Nat.find hab + 1) := by
      intro j
      constructor
      · calc
          a (j - (Nat.find hab + 1)) ≤ a (j - Nat.find hab) := by
            apply (aux_spacedSequence_monotone ha)
            omega
          _ ≤ b j := (Nat.find_spec hab j).1
          _ ≤ b (j + 1) := aux_spacedSequence_le_succ hb j
          _ = c j := (hc j).symm
      · rw [hc j]
        have h' := (Nat.find_spec hab (j + 1)).2
        simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using h'
    rw [show SequenceDistance a b = (Nat.find hab : WithTop ℕ) by simp [SequenceDistance, hab]]
    calc
      SequenceDistance a c ≤ ((Nat.find hab + 1 : ℕ) : WithTop ℕ) :=
        aux_sequenceDistance_le_of_within hwithin
      _ = (Nat.find hab : WithTop ℕ) + 1 := by simp
  · simp [SequenceDistance, hab]
end Auto
