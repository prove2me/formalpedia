-- Prove2me | solution 1 for ActuarialValuation.ratPurePremium_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:21:13.758742+00:00
-- url     : https://prove2.me/submissions/715af5b2-0289-4b01-95ba-6bd67eb8fde2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratPurePremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (loss exposure : ℝ) (hE : exposure ≠ 0) :
    ratPurePremium loss exposure * exposure = loss := by
  unfold ratPurePremium
  exact div_mul_cancel₀ loss hE
