-- Prove2me | solution 1 for ActuarialValuation.kmRiskExit_reconciliation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:57:26.841091+00:00
-- url     : https://prove2.me/submissions/cf64d465-b0df-47e7-9af8-62dd66bcc9ea

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmExitCount
import Definitions.Def_actuarial_kmDeathHazard
import Definitions.Def_actuarial_kmCensorHazard

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r d c : ℝ) (hr : r ≠ 0) :
    kmDeathHazard d r + kmCensorHazard c r = kmExitCount d c / r := by
  simp only [kmDeathHazard, kmCensorHazard, kmExitCount]
  rw [← add_div]
