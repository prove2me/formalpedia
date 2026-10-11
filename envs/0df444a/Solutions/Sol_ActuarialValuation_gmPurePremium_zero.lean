-- Prove2me | solution 1 for ActuarialValuation.gmPurePremium_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:15:07.608218+00:00
-- url     : https://prove2.me/submissions/87dfbe91-decd-4b38-85ab-9b8e2792beba

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmPurePremium
open ActuarialValuation

theorem solution(severity : ℝ) : gmPurePremium 0 severity=0 := by
  simp [gmPurePremium]
