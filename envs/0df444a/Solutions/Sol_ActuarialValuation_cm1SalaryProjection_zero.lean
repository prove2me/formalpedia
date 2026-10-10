-- Prove2me | solution 1 for ActuarialValuation.cm1SalaryProjection_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:02.47562+00:00
-- url     : https://prove2.me/submissions/5234df81-f7d2-4d04-8e72-03b5a6695562

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1SalaryProjection

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (base growth : ℝ) : cm1SalaryProjection base growth 0 = base := by
  simp [cm1SalaryProjection]
