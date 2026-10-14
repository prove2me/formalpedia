-- Prove2me | solution 1 for ActuarialValuation.alterationReserve_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:08:50.822987+00:00
-- url     : https://prove2.me/submissions/03db40ce-a57f-4d4a-814f-3a5d61f75a85

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationProspectiveReserve
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (B A P : ℝ) : alterationProspectiveReserve B A P + P*A = B := by
  unfold alterationProspectiveReserve
  ring
