-- Prove2me | solution 1 for ActuarialValuation.bdDuration_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:58:32.70374+00:00
-- url     : https://prove2.me/submissions/286c082c-674d-4eb1-8b71-99bdb6f1e55f

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdMacaulayDuration
import Definitions.Def_actuarial_bdCouponPV
import Definitions.Def_actuarial_bdDurationNumerator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D c : ℕ → ℝ) (n : ℕ) (h : bdCouponPV D c n ≠ 0) : bdMacaulayDuration D c n * bdCouponPV D c n = bdDurationNumerator D c n := by
  unfold bdMacaulayDuration
  field_simp [h] <;> ring
