-- Prove2me | solution 1 for ActuarialValuation.dbTrancheResidualPension_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:10:49.770094+00:00
-- url     : https://prove2.me/submissions/730a92e9-227a-41c8-af6f-4d9d5a17b4de

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbTrancheResidualPension

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (pension reduction : ℕ → ℝ) :
  dbTrancheResidualPension pension reduction 0 = 0 := by
  simp [dbTrancheResidualPension]
