-- Prove2me | solution 1 for ActuarialValuation.siFundStep_add_contribution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:59:50.05931+00:00
-- url     : https://prove2.me/submissions/0d7c0ee9-9c14-4e2f-8e76-7b05d8067c83

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFundStep

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (fund a b gross : ℝ) : siFundStep fund (a+b) gross=siFundStep fund a gross+b*gross := by
  unfold siFundStep
  ring
