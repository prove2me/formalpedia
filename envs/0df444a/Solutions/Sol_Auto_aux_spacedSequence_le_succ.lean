-- Prove2me | solution 1 for Auto.aux_spacedSequence_le_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:40:25.087571+00:00
-- url     : https://prove2.me/submissions/cd5dd690-e84b-44ab-b5de-7c5a7da7ce5f

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution {a : ℤ → ℝ} (ha : SpacedSequence a) (j : ℤ) :
    a j ≤ a (j + 1) := by
  have hpos := (ha j).1
  have hspace := (ha j).2
  nlinarith
end Auto
