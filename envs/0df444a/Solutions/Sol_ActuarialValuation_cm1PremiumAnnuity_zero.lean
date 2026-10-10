-- Prove2me | solution 1 for ActuarialValuation.cm1PremiumAnnuity_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:17:05.315053+00:00
-- url     : https://prove2.me/submissions/6a5e7b27-b533-41b5-882b-875eacad26fc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1PremiumAnnuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (d p : ℕ → ℝ) : cm1PremiumAnnuity d p 0 = 0 := by
  simp [cm1PremiumAnnuity]
