-- Prove2me | solution 1 for ActuarialValuation.pgSeverityPGF_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:43:54.533196+00:00
-- url     : https://prove2.me/submissions/a4474ee2-92fa-40a0-98ad-5ca2d9d0c84d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgSeverityPGF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (m : ℕ) (z : ℝ) : pgSeverityPGF f (m+1) z=pgSeverityPGF f m z+f (m+1)*z^(m+1) := by
  simp only [pgSeverityPGF, Finset.sum_range_succ]
