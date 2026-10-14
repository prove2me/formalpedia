-- Prove2me | solution 1 for ActuarialValuation.crRisk_at_least_q
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:56:38.83862+00:00
-- url     : https://prove2.me/submissions/3423b837-e48c-462f-b3bd-18dc1eebf3e2

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk
import Definitions.Def_actuarial_crExpected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p q X : Fin n→ℝ) : crExpected q X≤crScenarioRisk p q X := by
  unfold crScenarioRisk
  exact le_max_right _ _
