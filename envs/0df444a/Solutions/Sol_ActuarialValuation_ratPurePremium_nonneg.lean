-- Prove2me | solution 1 for ActuarialValuation.ratPurePremium_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:22:36.737973+00:00
-- url     : https://prove2.me/submissions/9fdb813b-0c96-41a7-9d16-07e5c019936c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratPurePremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (loss exposure : ℝ) (hL : 0 ≤ loss) (hE : 0 < exposure) :
    0 ≤ ratPurePremium loss exposure := by
  unfold ratPurePremium
  exact div_nonneg hL (le_of_lt hE)
