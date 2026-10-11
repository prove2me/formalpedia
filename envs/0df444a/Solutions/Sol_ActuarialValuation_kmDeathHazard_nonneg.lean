-- Prove2me | solution 1 for ActuarialValuation.kmDeathHazard_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:38:15.755697+00:00
-- url     : https://prove2.me/submissions/6b815cf6-0d3e-47c6-b580-630de3ae1f80

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmDeathHazard
open ActuarialValuation

theorem solution(d r : ℝ) (hd : 0 ≤ d) (hr : 0 < r) : 0 ≤ kmDeathHazard d r := by
  unfold kmDeathHazard
  exact div_nonneg hd hr.le
