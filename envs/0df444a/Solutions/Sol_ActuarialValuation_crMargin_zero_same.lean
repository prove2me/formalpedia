-- Prove2me | solution 1 for ActuarialValuation.crMargin_zero_same
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:22:52.630676+00:00
-- url     : https://prove2.me/submissions/5bcbc6a2-ca57-4fa5-8014-0b785cd87d29

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpectationMargin
open ActuarialValuation

theorem solution{n : ℕ} (p X : Fin n→ℝ) : crExpectationMargin p p X=0 := by
  simp [crExpectationMargin]
