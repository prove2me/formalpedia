-- Prove2me | solution 1 for ActuarialValuation.scrPairSquared_uncorrelated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:36:16.211672+00:00
-- url     : https://prove2.me/submissions/31eccbdc-26be-40c8-b69a-6ca58870ab1d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPairSquared
import Definitions.Def_actuarial_scrUncorrelatedSquared

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b : ℝ) : scrPairSquared 0 a b = scrUncorrelatedSquared a b := by
  simp [scrPairSquared, scrCovarianceTerm, scrUncorrelatedSquared]
