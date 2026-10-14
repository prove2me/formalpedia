-- Prove2me | solution 1 for ActuarialValuation.crRisk_at_least_p
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:56:27.423608+00:00
-- url     : https://prove2.me/submissions/fc831e1f-fce9-46a7-8da8-95ce46f6e734

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk
import Definitions.Def_actuarial_crExpected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p q X : Fin n→ℝ) : crExpected p X≤crScenarioRisk p q X := by
  unfold crScenarioRisk
  exact le_max_left _ _
