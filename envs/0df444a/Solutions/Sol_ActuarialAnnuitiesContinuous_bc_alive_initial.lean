-- Prove2me | solution 1 for ActuarialAnnuitiesContinuous.bc_alive_initial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:08:39.236315+00:00
-- url     : https://prove2.me/submissions/5f46fea3-a7ca-43dc-a054-70ded5284949

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcAlive

open ActuarialAnnuitiesContinuous

open MeasureTheory

theorem solution (lifetime t : ℝ) (ht : t ≤ lifetime) : bcAlive lifetime t = 1 := by
  unfold bcAlive; rw [if_pos ht]


