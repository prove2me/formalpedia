-- Prove2me | solution 1 for ActuarialValuation.lcExpectedDeathCost_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:39:26.197484+00:00
-- url     : https://prove2.me/submissions/270d7a1a-cc9d-485d-8268-e1e433649632

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_lcExpectedDeathCost
import Definitions.Def_actuarial_lcPeriodDeaths

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lives q b : ℝ) :
    lcExpectedDeathCost lives q b = lives * (q * b) := by
  unfold lcExpectedDeathCost lcPeriodDeaths
  ring
