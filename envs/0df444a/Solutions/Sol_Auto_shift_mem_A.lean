-- Prove2me | solution 1 for Auto.shift_mem_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:03:33.898989+00:00
-- url     : https://prove2.me/submissions/0fe35f25-3aa9-4a7d-a695-34ab9f18003a

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution {a : ℤ → ℝ} (ha : SpacedSequence a) (n : ℤ) :
    SpacedSequence (fun j => a (j + n)) := by
  intro j
  constructor
  · exact (ha (j + n)).1
  · convert (ha (j + n)).2 using 1; ring_nf
end Auto
