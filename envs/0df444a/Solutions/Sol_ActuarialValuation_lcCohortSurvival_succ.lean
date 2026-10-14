-- Prove2me | solution 1 for ActuarialValuation.lcCohortSurvival_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:26:18.148533+00:00
-- url     : https://prove2.me/submissions/0583c308-bb00-4a9b-9bb1-81b82cc04ae0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcCohortSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (q : ℕ → ℝ) (n : ℕ) :
    lcCohortSurvival q (n+1) =
      lcCohortSurvival q n * (1-q n) := by
  simp [lcCohortSurvival, Finset.prod_range_succ]
