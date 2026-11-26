-- Prove2me | solution 1 for Auto.aux_pow_two_mul_le_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:40:25.73849+00:00
-- url     : https://prove2.me/submissions/262412d7-1ef8-4d98-b9b6-545a0332f2d8

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution {a : ℤ → ℝ} (ha : SpacedSequence a) (j : ℤ) (k : ℕ) :
    (2 : ℝ) ^ k * a j ≤ a (j + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := (ha (j + k)).2
      have hmul : 2 * ((2 : ℝ) ^ k * a j) ≤ 2 * a (j + k) := by
        gcongr
      calc
        (2 : ℝ) ^ (Nat.succ k) * a j = 2 * ((2 : ℝ) ^ k * a j) := by
          rw [pow_succ]
          ring
        _ ≤ 2 * a (j + k) := hmul
        _ ≤ a (j + Nat.succ k) := by
          convert hstep using 1; push_cast; ring_nf
end Auto
