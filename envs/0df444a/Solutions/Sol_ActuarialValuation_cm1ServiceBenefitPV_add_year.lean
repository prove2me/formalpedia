-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceBenefitPV_add_year
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:27:09.358844+00:00
-- url     : https://prove2.me/submissions/32d1d10d-e924-47eb-8ce9-f027f3a0647e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceCohortCause
import Definitions.Def_actuarial_cm1ServiceBenefitPV
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (v : ℕ → ℝ) (b d : ℕ → ℕ → ℝ) (l : ℕ → ℝ) (N m : ℕ) : cm1ServiceBenefitPV v b d l (N+1) m = cm1ServiceBenefitPV v b d l N m + (∑ j ∈ Finset.range m, v N * b N j * cm1ServiceCohortCause l d N j) := by
  simp [cm1ServiceBenefitPV, Finset.sum_range_succ]
