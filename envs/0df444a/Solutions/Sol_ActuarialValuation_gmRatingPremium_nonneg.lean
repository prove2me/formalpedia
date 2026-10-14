-- Prove2me | solution 1 for ActuarialValuation.gmRatingPremium_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:29:43.292014+00:00
-- url     : https://prove2.me/submissions/49f8fbfd-0990-4d31-a80c-37c919599872

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmMean
import Definitions.Def_actuarial_gmRatingPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (exposure eta severity : ℝ)
    (he : 0 ≤ exposure) (hs : 0 ≤ severity) :
    0 ≤ gmRatingPremium exposure eta severity := by
  unfold gmRatingPremium gmMean
  exact mul_nonneg (mul_nonneg he (Real.exp_pos eta).le) hs
