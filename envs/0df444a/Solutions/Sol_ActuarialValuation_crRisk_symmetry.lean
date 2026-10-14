-- Prove2me | solution 1 for ActuarialValuation.crRisk_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:22:12.189338+00:00
-- url     : https://prove2.me/submissions/3c65a21c-f653-43cc-b756-e35e5c289498

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk
open ActuarialValuation

theorem solution{n : ℕ} (p q X : Fin n→ℝ) : crScenarioRisk p q X = crScenarioRisk q p X := by
  unfold crScenarioRisk
  exact max_comm _ _
