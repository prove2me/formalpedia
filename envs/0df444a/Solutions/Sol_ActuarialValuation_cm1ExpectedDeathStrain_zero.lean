-- Prove2me | solution 1 for ActuarialValuation.cm1ExpectedDeathStrain_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:19:08.40977+00:00
-- url     : https://prove2.me/submissions/51ca113e-cdeb-443f-a808-dacda65c196e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ExpectedDeathStrain

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (S : ℝ) : cm1ExpectedDeathStrain 0 S = 0 := by
  simp [cm1ExpectedDeathStrain]
