-- Prove2me | solution 1 for ActuarialValuation.cm1RetrospectiveCashReserve_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:52.561955+00:00
-- url     : https://prove2.me/submissions/059ef099-c315-4e23-b9f8-ef5289d5c72a

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1RetrospectiveCashReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (P O : ℝ) : cm1RetrospectiveCashReserve P O + O = P := by
  unfold cm1RetrospectiveCashReserve
  ring
