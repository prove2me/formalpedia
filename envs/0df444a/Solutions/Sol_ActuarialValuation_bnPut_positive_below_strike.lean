-- Prove2me | solution 1 for ActuarialValuation.bnPut_positive_below_strike
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:10:40.059895+00:00
-- url     : https://prove2.me/submissions/0203c2c4-0719-423f-87a4-83e0263a9c7e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnPut
open ActuarialValuation

theorem solution(s k : ℝ) (h : s ≤ k) : bnPut s k = k-s := by
  unfold bnPut
  exact max_eq_left (by linarith)
