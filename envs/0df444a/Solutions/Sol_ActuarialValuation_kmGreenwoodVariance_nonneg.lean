-- Prove2me | solution 1 for ActuarialValuation.kmGreenwoodVariance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:20:10.745984+00:00
-- url     : https://prove2.me/submissions/83d9387e-068d-455d-8cfc-54ab58ea19dc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmGreenwoodSum
import Definitions.Def_actuarial_kmGreenwoodVariance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r d : ℕ → ℝ) (n : ℕ) (h : 0 ≤ kmGreenwoodSum r d n) :
    0 ≤ kmGreenwoodVariance r d n := by
  unfold kmGreenwoodVariance
  exact mul_nonneg (sq_nonneg (kmSurvival r d n)) h
