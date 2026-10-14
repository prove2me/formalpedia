-- Prove2me | solution 1 for ActuarialValuation.gmObservedRate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:32:03.509236+00:00
-- url     : https://prove2.me/submissions/d94d2b6c-51b5-4858-b861-0a2ea3cd4858

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Positivity
import Definitions.Def_actuarial_gmObservedRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claims exposure : ℝ) (hc : 0 ≤ claims)
    (hE : 0 < exposure) : 0 ≤ gmObservedRate claims exposure := by
  unfold gmObservedRate
  exact div_nonneg hc hE.le
