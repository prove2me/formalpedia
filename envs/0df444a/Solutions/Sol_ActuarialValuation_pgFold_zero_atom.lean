-- Prove2me | solution 1 for ActuarialValuation.pgFold_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:07:05.09498+00:00
-- url     : https://prove2.me/submissions/ba6b1c81-6030-4969-a7c3-353895e6d51d

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgFold
open ActuarialValuation

theorem solution(f : ℕ → ℝ) (n : ℕ) : pgFold f n 0 = (f 0)^n := by
  induction n with
  | zero => simp [pgFold, pgPointMass]
  | succ n ih =>
    show pgConvolve f (pgFold f n) 0 = f 0 ^ (n + 1)
    simp [pgConvolve, ih, pow_succ, mul_comm]
