-- Prove2me | solution 1 for ActuarialAnnuitiesBridge.bridge_continuous_due_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:08:24.670405+00:00
-- url     : https://prove2.me/submissions/182c4342-8d30-4c58-b551-7bba411c6b37

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcLeftRiemann


open MeasureTheory

theorem solution (m : ℕ) (f : ℝ → ℝ) : ActuarialAnnuitiesContinuous.bcLeftRiemann 0 m f = 0 := by
  unfold ActuarialAnnuitiesContinuous.bcLeftRiemann; simp


