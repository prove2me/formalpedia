-- Prove2me | solution 1 for ActuarialValuation.pgFold_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:34:17.029604+00:00
-- url     : https://prove2.me/submissions/10eee010-3298-4235-af2f-7bc6211ad52c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgFold
open ActuarialValuation

theorem solution(f : ℕ → ℝ) (n k : ℕ) (h : ∀ j, 0 ≤ f j) : 0 ≤ pgFold f n k := by
  induction n generalizing k with
  | zero =>
    show 0 ≤ pgPointMass k
    unfold pgPointMass
    split_ifs <;> norm_num
  | succ n ih =>
    show 0 ≤ pgConvolve f (pgFold f n) k
    unfold pgConvolve
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (h j) (ih _))
