-- Prove2me | solution 1 for ActuarialValuation.cm1ExpectedBenefitPV_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:16:49.709018+00:00
-- url     : https://prove2.me/submissions/634b4c72-0cf2-4e85-828d-862f389df682

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ExpectedBenefitPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b d p : ℕ → ℝ) : cm1ExpectedBenefitPV b d p 0 = 0 := by
  simp [cm1ExpectedBenefitPV]
