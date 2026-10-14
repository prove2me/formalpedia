-- Prove2me | solution 1 for ActuarialValuation.lcCohortLives_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:14:17.303984+00:00
-- url     : https://prove2.me/submissions/577ef8db-e378-4874-a1a8-c531e6b4c98c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcCohortLives

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (initial : ℝ) (q : ℕ → ℝ) (n : ℕ) :
    lcCohortLives initial q (n+1) =
      lcCohortLives initial q n * (1-q n) := by
  simp [lcCohortLives, lcCohortSurvival, Finset.prod_range_succ, mul_assoc]
