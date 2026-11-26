-- Prove2me | solution 1 for Auto.aux_spacedSequence_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:58:54.942658+00:00
-- url     : https://prove2.me/submissions/de52bf12-67a9-49e7-a34c-1407685fcc48

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution {a : ℤ → ℝ} (ha : SpacedSequence a) (j : ℤ) : 0 < a j :=
  (ha j).1
end Auto
