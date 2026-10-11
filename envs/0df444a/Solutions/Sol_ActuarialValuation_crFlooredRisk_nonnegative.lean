-- Prove2me | solution 1 for ActuarialValuation.crFlooredRisk_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:53:06.649087+00:00
-- url     : https://prove2.me/submissions/c548743d-0dc4-4671-8687-7e8f2ea31ae3

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crFlooredRisk
open ActuarialValuation

theorem solution{n : ℕ} (p q X : Fin n→ℝ) : 0≤crFlooredRisk p q X := by
  unfold crFlooredRisk
  exact le_max_left _ _
