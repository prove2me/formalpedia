-- Prove2me | solution 1 for ActuarialValuation.crLoading_singleton
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:57:14.137956+00:00
-- url     : https://prove2.me/submissions/cfefd473-2ba4-4a84-bd14-5f7d39d824f3

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crLoading

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p X : Fin n→ℝ) : crLoading p p X=0 := by
  simp [crLoading, crScenarioRisk]
