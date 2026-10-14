-- Prove2me | solution 1 for ActuarialValuation.pgCountPGF_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:42:34.5559+00:00
-- url     : https://prove2.me/submissions/a2a2ed4c-7f78-49be-8006-befeba8ee08f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgCountPGF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (m : ℕ) (z : ℝ) : pgCountPGF p (m+1) z=pgCountPGF p m z+p (m+1)*z^(m+1) := by
  simp only [pgCountPGF, Finset.sum_range_succ]
