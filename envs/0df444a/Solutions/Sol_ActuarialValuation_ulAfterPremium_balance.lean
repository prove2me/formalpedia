-- Prove2me | solution 1 for ActuarialValuation.ulAfterPremium_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:03:16.120989+00:00
-- url     : https://prove2.me/submissions/28e3cbb7-7ef2-4925-a64b-d324c02dcf9c

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAfterPremium
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_ulAllocatedPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (account prem expense flat : ℝ) : ulAfterPremium account prem expense flat + flat = account + ulAllocatedPremium prem expense := by
  unfold ulAfterPremium
  ring
