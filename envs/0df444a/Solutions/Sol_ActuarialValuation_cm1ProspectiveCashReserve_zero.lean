-- Prove2me | solution 1 for ActuarialValuation.cm1ProspectiveCashReserve_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:11.029801+00:00
-- url     : https://prove2.me/submissions/83fcc162-f25e-4838-8908-d68ed2195583

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ProspectiveCashReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (B E : ℝ) : cm1ProspectiveCashReserve B E 0 = B+E := by
  simp [cm1ProspectiveCashReserve]
