-- Prove2me | solution 1 for ActuarialValuation.ratRelativity_unit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:58:21.912863+00:00
-- url     : https://prove2.me/submissions/5b8e1fed-a5a4-49b5-8293-9f08181e2e7b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratRelativity
open ActuarialValuation

theorem solution(base : ℝ) (hb : base ≠ 0) : ratRelativity base base = 1 := by
  simp [ratRelativity, hb]
