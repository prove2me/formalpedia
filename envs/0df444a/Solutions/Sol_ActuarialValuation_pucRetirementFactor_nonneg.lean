-- Prove2me | solution 1 for ActuarialValuation.pucRetirementFactor_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:19:47.605181+00:00
-- url     : https://prove2.me/submissions/e993229a-524f-4e8d-af6a-bc4f54e9a284

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucRetirementFactor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p v ann : ℝ) (hp : 0 ≤ p) (hv : 0 ≤ v) (ha : 0 ≤ ann) : 0 ≤ pucRetirementFactor p v ann := by
  unfold pucRetirementFactor
  exact mul_nonneg (mul_nonneg hp hv) ha
