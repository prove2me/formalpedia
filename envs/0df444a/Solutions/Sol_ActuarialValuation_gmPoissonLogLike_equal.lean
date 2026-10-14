-- Prove2me | solution 1 for ActuarialValuation.gmPoissonLogLike_equal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:35:35.815484+00:00
-- url     : https://prove2.me/submissions/6863e38b-dd0d-42f3-8d05-cb0efa0fc85b

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmPoissonLogLike
import Definitions.Def_actuarial_gmSaturatedLike

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claims expected : ℝ) (h : claims = expected) :
    gmPoissonLogLike claims expected = gmSaturatedLike claims := by
  subst expected
  rfl
