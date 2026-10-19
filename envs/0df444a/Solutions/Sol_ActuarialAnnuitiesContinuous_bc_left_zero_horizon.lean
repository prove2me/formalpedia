-- Prove2me | solution 1 for ActuarialAnnuitiesContinuous.bc_left_zero_horizon
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:09:21.681101+00:00
-- url     : https://prove2.me/submissions/dd05d8a6-67e6-41d0-8959-dbe9fb78cf00

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcLeftRiemann

open ActuarialAnnuitiesContinuous

open MeasureTheory

theorem solution (m : ℕ) (f : ℝ → ℝ) : bcLeftRiemann 0 m f = 0 := by
  unfold bcLeftRiemann; simp


