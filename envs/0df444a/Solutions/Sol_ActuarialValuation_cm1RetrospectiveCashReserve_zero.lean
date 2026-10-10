-- Prove2me | solution 1 for ActuarialValuation.cm1RetrospectiveCashReserve_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:46.097644+00:00
-- url     : https://prove2.me/submissions/a05abedf-9838-474e-a4cd-f5f391338956

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1RetrospectiveCashReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (P : ℝ) : cm1RetrospectiveCashReserve P 0 = P := by
  simp [cm1RetrospectiveCashReserve]
