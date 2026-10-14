-- Prove2me | solution 1 for ActuarialValuation.ulTypeB_mortality_cost_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:14:57.037666+00:00
-- url     : https://prove2.me/submissions/1c5ba87e-5fa2-48ed-a300-4ed01791a00f

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulTypeBNext
import Definitions.Def_actuarial_ulEarned
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (account prem expense flat interest mortality face : ℝ) (hm : 0≤mortality) (hf : 0≤face) : ulTypeBNext account prem expense flat interest mortality face ≤ ulEarned account prem expense flat interest := by
  change ulEarned account prem expense flat interest - mortality * face ≤
    ulEarned account prem expense flat interest
  nlinarith [mul_nonneg hm hf]
