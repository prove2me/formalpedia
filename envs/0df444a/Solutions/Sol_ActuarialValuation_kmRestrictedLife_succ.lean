-- Prove2me | solution 1 for ActuarialValuation.kmRestrictedLife_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:38:23.232713+00:00
-- url     : https://prove2.me/submissions/51819ce4-e8a6-4653-9003-afa220036be7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvival
import Definitions.Def_actuarial_kmRestrictedLife

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r d : ℕ → ℝ) (n : ℕ) :
    kmRestrictedLife r d (n+1) = kmRestrictedLife r d n + kmSurvival r d n := by
  simp [kmRestrictedLife, Finset.sum_range_succ]
