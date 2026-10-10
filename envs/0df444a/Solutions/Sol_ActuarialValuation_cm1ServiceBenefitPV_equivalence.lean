-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceBenefitPV_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:58:46.864742+00:00
-- url     : https://prove2.me/submissions/710270ca-cbd6-47ad-a46c-86a046418f02

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceBenefitPV
import Definitions.Def_actuarial_cm1ServiceConditionalPV
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (v : ℕ → ℝ) (b d : ℕ → ℕ → ℝ) (l : ℕ → ℝ) (N m : ℕ) (h0 : l 0 ≠ 0) (hpos : ∀ t ∈ Finset.range N, l t ≠ 0) : cm1ServiceBenefitPV v b d l N m = cm1ServiceConditionalPV v b d l N m := by
  unfold cm1ServiceBenefitPV cm1ServiceConditionalPV
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro j hj
  have htne := hpos t ht
  unfold cm1ServiceCohortCause cm1ServiceSurvivalMass cm1ServiceConditionalCause
  field_simp [h0, htne]
