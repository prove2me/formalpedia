-- Prove2me | solution 1 for Auto.aux_pow_two_mul_shift_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:58:57.060316+00:00
-- url     : https://prove2.me/submissions/bb63feec-0b43-4c69-8fbe-9d000f6963e9

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
public import Theorems.Thm_Auto_aux_pow_two_mul_le_shift

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution {a : ℤ → ℝ} (ha : SpacedSequence a) (j : ℤ) (k : ℕ) :
    (2 : ℝ) ^ k * a (j - k) ≤ a j := by
  convert aux_pow_two_mul_le_shift ha (j - k) k using 1; ring_nf
end Auto
