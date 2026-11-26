-- Prove2me | solution 1 for Auto.aux_withinSequenceDistance_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:03:43.920807+00:00
-- url     : https://prove2.me/submissions/1353bd76-578d-41a1-983e-aae31fa3a285

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution {a b c : ℤ → ℝ} {k : ℕ}
    (hab : WithinSequenceDistance a b k) (hac : WithinSequenceDistance a c k) :
    WithinSequenceDistance a (fun j => max (b j) (c j)) k := by
  intro j
  constructor
  · exact (hab j).1.trans (le_max_left _ _)
  · exact max_le (hab j).2 (hac j).2
end Auto
