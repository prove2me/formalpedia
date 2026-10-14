-- Prove2me | solution 1 for ActuarialValuation.kmRemainingRisk_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:42:00.349364+00:00
-- url     : https://prove2.me/submissions/e384cb23-de4b-45f9-94c8-f515a8bf62b5

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmRemainingRisk
import Definitions.Def_actuarial_kmExitCount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r d c : ℝ) : kmRemainingRisk r d c + kmExitCount d c = r := by
  simp [kmRemainingRisk, kmExitCount]
