-- Prove2me | solution 1 for ActuarialValuation.pgAggregate_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:49:34.084419+00:00
-- url     : https://prove2.me/submissions/75bb2b35-0583-4299-951c-6ad6667fdc9a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgAggregate
import Definitions.Def_actuarial_pgCountPGF
open ActuarialValuation

theorem solution(p f : ℕ → ℝ) (m : ℕ) : pgAggregate p f m 0=pgCountPGF p m (f 0) := by
  have key : ∀ j, pgFold f j 0 = f 0 ^ j := by
    intro j
    induction j with
    | zero => simp [pgFold, pgPointMass]
    | succ j ih =>
      show pgConvolve f (pgFold f j) 0 = _
      simp [pgConvolve, ih, pow_succ]
      ring
  unfold pgAggregate pgCountPGF
  apply Finset.sum_congr rfl
  intro j _
  rw [key]
