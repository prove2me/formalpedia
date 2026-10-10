-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceCauseCohort_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:58:55.859845+00:00
-- url     : https://prove2.me/submissions/9398ae7a-39cb-4e1f-9c3f-891a116257c0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceSurvivalMass
import Definitions.Def_actuarial_cm1ServiceConditionalCause
import Definitions.Def_actuarial_cm1ServiceCohortCause
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (d : ℕ → ℕ → ℝ) (t j : ℕ) (h0 : l 0 ≠ 0) (ht : l t ≠ 0) : cm1ServiceSurvivalMass l t * cm1ServiceConditionalCause l d t j = cm1ServiceCohortCause l d t j := by
  change (l t / l 0) * (d t j / l t) = d t j / l 0
  field_simp [h0, ht]
