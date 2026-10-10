-- Prove2me | solution 1 for ActuarialValuation.cm1ExpectedDeathStrain_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:19:15.196474+00:00
-- url     : https://prove2.me/submissions/b19ce69a-645d-43fe-96a4-363ae82565b0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ExpectedDeathStrain

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (q S : ℝ) (hq : 0 ≤ q) (hS : 0 ≤ S) : 0 ≤ cm1ExpectedDeathStrain q S := by
  unfold cm1ExpectedDeathStrain
  exact mul_nonneg hq hS
