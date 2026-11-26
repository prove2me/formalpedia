-- Prove2me | solution 1 for Auto.max_mem_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:03:31.429515+00:00
-- url     : https://prove2.me/submissions/04490b7c-c13d-47ff-98a1-99058711ff8e

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
public import Theorems.Thm_Auto_aux_spacedSequence_pos

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution {a b : ℤ → ℝ} (ha : SpacedSequence a) (hb : SpacedSequence b) :
    SpacedSequence (fun j => max (a j) (b j)) := by
  intro j
  constructor
  · exact lt_of_lt_of_le (aux_spacedSequence_pos ha j) (le_max_left _ _)
  · change 2 * max (a j) (b j) ≤ max (a (j + 1)) (b (j + 1))
    by_cases hab : a j ≤ b j
    · rw [max_eq_right hab]
      exact (hb j).2.trans (le_max_right _ _)
    · rw [max_eq_left (le_of_not_ge hab)]
      exact (ha j).2.trans (le_max_left _ _)
end Auto
