-- Prove2me | solution 1 for ActuarialValuation.cm1PensionCapitalValue_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:46:41.543635+00:00
-- url     : https://prove2.me/submissions/b6d653e0-a7c2-4c5b-a6e0-d15a4a55a2f9

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1PensionCapitalValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p a : ℝ) (hp : 0 ≤ p) (ha : 0 ≤ a) : 0 ≤ cm1PensionCapitalValue p a := by
  simp only [cm1PensionCapitalValue]
  exact mul_nonneg hp ha
