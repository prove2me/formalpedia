-- Prove2me | solution 1 for ActuarialValuation.kmSurvivalStep_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:56:14.529977+00:00
-- url     : https://prove2.me/submissions/b0abe6f4-a4e2-4392-a75b-78ab7e2d97a2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvival
import Definitions.Def_actuarial_kmSurvivalStep

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r d : ℕ → ℝ) (n : ℕ) :
    kmSurvivalStep (kmSurvival r d n) (d n) (r n) = kmSurvival r d (n+1) := by
  simp [kmSurvivalStep, kmSurvival, Finset.prod_range_succ, kmSurvivalFactor, kmDeathHazard]
