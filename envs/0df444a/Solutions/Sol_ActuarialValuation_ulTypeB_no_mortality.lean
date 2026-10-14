-- Prove2me | solution 1 for ActuarialValuation.ulTypeB_no_mortality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:14:45.865734+00:00
-- url     : https://prove2.me/submissions/2fe12b02-5104-48da-adfb-eab2d2327723

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulTypeBNext
import Definitions.Def_actuarial_ulEarned

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (account prem expense flat interest face : ℝ) : ulTypeBNext account prem expense flat interest 0 face = ulEarned account prem expense flat interest := by
  simp [ulTypeBNext]
