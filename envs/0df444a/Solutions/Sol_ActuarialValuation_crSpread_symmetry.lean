-- Prove2me | solution 1 for ActuarialValuation.crSpread_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:57:27.046701+00:00
-- url     : https://prove2.me/submissions/3ba2b636-67af-4d5b-abbf-3e8c1581cad6

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crAmbiguitySpread

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p q X : Fin n→ℝ) : crAmbiguitySpread p q X = crAmbiguitySpread q p X := by
  simp [crAmbiguitySpread, crScenarioRisk, crBestCaseRisk, max_comm, min_comm]
