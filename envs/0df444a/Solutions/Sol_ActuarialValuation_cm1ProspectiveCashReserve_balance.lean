-- Prove2me | solution 1 for ActuarialValuation.cm1ProspectiveCashReserve_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:17.81913+00:00
-- url     : https://prove2.me/submissions/d948dfb4-c82a-4a93-854f-c69f07fe195b

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ProspectiveCashReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (B E P : ℝ) : cm1ProspectiveCashReserve B E P + P = B + E := by
  unfold cm1ProspectiveCashReserve
  ring
