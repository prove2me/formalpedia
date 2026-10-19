-- Prove2me | solution 1 for ActuarialAnnuitiesContinuous.bc_continuous_zero_rate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:08:55.828343+00:00
-- url     : https://prove2.me/submissions/9f3b42c2-792e-4c81-878f-ec8869f290d8

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcExpectedPV

open ActuarialAnnuitiesContinuous

open MeasureTheory

theorem solution (N : ℕ) (p : ℕ → ℝ) (life : ℕ → ℝ) (a term g rho : ℝ) : bcExpectedPV N p life a term g rho (fun _ => 0) = 0 := by
  unfold bcExpectedPV bcPathPV; simp


