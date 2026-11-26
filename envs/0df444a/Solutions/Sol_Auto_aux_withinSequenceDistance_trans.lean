-- Prove2me | solution 1 for Auto.aux_withinSequenceDistance_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:59:37.138019+00:00
-- url     : https://prove2.me/submissions/01777dc1-37a1-47f8-b517-974e5e59d03b

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution {a b c : ℤ → ℝ} {k l : ℕ}
    (hab : WithinSequenceDistance a b k) (hbc : WithinSequenceDistance b c l) :
    WithinSequenceDistance a c (k + l) := by
  intro j
  constructor
  · calc
      a (j - (k + l)) = a ((j - l) - k) := by ring_nf
      _ ≤ b (j - l) := (hab (j - l)).1
      _ ≤ c j := (hbc j).1
  · calc
      c j ≤ b (j + l) := (hbc j).2
      _ ≤ a ((j + l) + k) := (hab (j + l)).2
      _ = a (j + (k + l)) := by ring_nf
end Auto
