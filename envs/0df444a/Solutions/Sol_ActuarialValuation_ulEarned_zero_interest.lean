-- Prove2me | solution 1 for ActuarialValuation.ulEarned_zero_interest
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:13:59.259256+00:00
-- url     : https://prove2.me/submissions/c27e5615-3ef8-4403-8eb2-bfc1bcbcec69

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulEarned
import Definitions.Def_actuarial_ulAfterPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (account prem expense flat : ℝ) : ulEarned account prem expense flat 0 = ulAfterPremium account prem expense flat := by
  simp [ulEarned]
