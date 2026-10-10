-- Prove2me | solution 1 for ActuarialValuation.cm1NonUnitCashflow_no_claims
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:20:22.86893+00:00
-- url     : https://prove2.me/submissions/e9fab04c-932f-49d4-8df5-ec13ea0eef6b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1NonUnitCashflow

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (P C E : ℝ) : cm1NonUnitCashflow P C E 0 = P+C-E := by
  simp [cm1NonUnitCashflow]
