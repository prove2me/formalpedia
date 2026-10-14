-- Prove2me | solution 1 for ActuarialValuation.crRisk_attained
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:07:50.706044+00:00
-- url     : https://prove2.me/submissions/b6ea80ed-3d19-4318-8361-f2362dbec1db

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk
import Definitions.Def_actuarial_crWorstCaseDistribution
import Definitions.Def_actuarial_crExpected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p q X : Fin n→ℝ) : crScenarioRisk p q X = crExpected (crWorstCaseDistribution p q X) X := by
  unfold crScenarioRisk crWorstCaseDistribution
  by_cases h : crExpected p X ≤ crExpected q X
  · simp [h, max_eq_right h]
  · have h' : crExpected q X ≤ crExpected p X := le_of_not_ge h
    simp [h, max_eq_left h']
