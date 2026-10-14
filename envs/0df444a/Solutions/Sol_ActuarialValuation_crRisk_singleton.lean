-- Prove2me | solution 1 for ActuarialValuation.crRisk_singleton
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:56:50.868702+00:00
-- url     : https://prove2.me/submissions/d607e1b1-98f0-439e-9548-947dee54f427

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk
import Definitions.Def_actuarial_crExpected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p X : Fin n→ℝ) : crScenarioRisk p p X = crExpected p X := by
  simp [crScenarioRisk]
