-- Prove2me | solution 1 for Auto.aux_spacedSequence_monotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:41:36.871485+00:00
-- url     : https://prove2.me/submissions/4fe74a7d-7618-4094-b9cc-9937ab007157

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
public import Theorems.Thm_Auto_aux_spacedSequence_le_succ

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution {a : ℤ → ℝ} (ha : SpacedSequence a) : Monotone a :=
  monotone_int_of_le_succ (aux_spacedSequence_le_succ ha)
end Auto
