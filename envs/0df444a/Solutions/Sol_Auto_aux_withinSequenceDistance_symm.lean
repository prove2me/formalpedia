-- Prove2me | solution 1 for Auto.aux_withinSequenceDistance_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:59:29.522564+00:00
-- url     : https://prove2.me/submissions/f5165934-8879-4579-b919-e42ee9ff60be

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution {a b : ℤ → ℝ} {k : ℕ} :
    WithinSequenceDistance a b k ↔ WithinSequenceDistance b a k := by
  constructor <;> intro h <;> intro j
  · constructor
    · have h' := (h (j - k)).2
      convert h' using 1; ring_nf
    · have h' := (h (j + k)).1
      convert h' using 1; ring_nf
  · constructor
    · have h' := (h (j - k)).2
      convert h' using 1; ring_nf
    · have h' := (h (j + k)).1
      convert h' using 1; ring_nf
end Auto
