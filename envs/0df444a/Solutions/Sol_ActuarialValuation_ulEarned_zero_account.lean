-- Prove2me | solution 1 for ActuarialValuation.ulEarned_zero_account
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:14:10.864118+00:00
-- url     : https://prove2.me/submissions/b5dd8816-0e78-4f37-bc96-a557cc2377e1

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulEarned
import Definitions.Def_actuarial_ulAllocatedPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (prem expense flat interest : ℝ) : ulEarned 0 prem expense flat interest = (ulAllocatedPremium prem expense-flat)*(1+interest) := by
  simp [ulEarned, ulAfterPremium]
