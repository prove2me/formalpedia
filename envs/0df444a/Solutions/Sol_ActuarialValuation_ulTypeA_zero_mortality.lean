-- Prove2me | solution 1 for ActuarialValuation.ulTypeA_zero_mortality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:15:10.300214+00:00
-- url     : https://prove2.me/submissions/db0f199b-269b-4918-9db3-7c018fd8a20b

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulTypeANext
import Definitions.Def_actuarial_ulEarned

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (account prem expense flat interest face : ℝ) : ulTypeANext account prem expense flat interest 0 face = ulEarned account prem expense flat interest := by
  simp [ulTypeANext]
