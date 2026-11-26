-- Prove2me | solution 1 for Auto.smul_mem_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:03:33.264335+00:00
-- url     : https://prove2.me/submissions/c602706b-4374-4d5b-a270-696537f097b5

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution {a : ℤ → ℝ} (ha : SpacedSequence a) {t : ℝ} (ht : 0 < t) :
    SpacedSequence (fun j => t * a j) := by
  intro j
  constructor
  · exact mul_pos ht (ha j).1
  · calc
      2 * (t * a j) = t * (2 * a j) := by ring
      _ ≤ t * a (j + 1) := by gcongr; exact (ha j).2
end Auto
