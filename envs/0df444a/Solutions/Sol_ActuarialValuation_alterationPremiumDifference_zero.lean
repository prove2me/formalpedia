-- Prove2me | solution 1 for ActuarialValuation.alterationPremiumDifference_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:13:42.50399+00:00
-- url     : https://prove2.me/submissions/6fe5c523-11b0-45e0-a51c-e83214d8083c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationPremiumDifference

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (P A : ℝ) : alterationPremiumDifference P P A = 0 := by
  simp [alterationPremiumDifference]
