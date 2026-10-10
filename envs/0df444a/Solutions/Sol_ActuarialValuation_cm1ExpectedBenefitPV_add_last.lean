-- Prove2me | solution 1 for ActuarialValuation.cm1ExpectedBenefitPV_add_last
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:02.840861+00:00
-- url     : https://prove2.me/submissions/5f6ae494-f912-47ce-96ed-2c05f2d4c36a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ExpectedBenefitPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b d p : ℕ → ℝ) (N : ℕ) : cm1ExpectedBenefitPV b d p (N+1) = cm1ExpectedBenefitPV b d p N + b N*d N*p N := by
  simp only [cm1ExpectedBenefitPV, Finset.sum_range_succ]
