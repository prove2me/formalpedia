-- Prove2me | solution 1 for ActuarialValuation.crLoading_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:09:02.510987+00:00
-- url     : https://prove2.me/submissions/acb65fff-4403-49cf-a6f6-9d136028832d

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crLoading
open ActuarialValuation

theorem solution{n : ℕ} (p q X : Fin n→ℝ) : 0≤crLoading p q X := by
  unfold crLoading crScenarioRisk
  linarith [le_max_left (crExpected p X) (crExpected q X)]
