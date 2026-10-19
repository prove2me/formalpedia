-- Prove2me | solution 1 for ActuarialAnnuitiesContinuous.bc_alive_postdeath
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:08:47.441825+00:00
-- url     : https://prove2.me/submissions/432d62a8-1d7f-47f9-8c3f-2d8577b6f924

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcAlive

open ActuarialAnnuitiesContinuous

open MeasureTheory

theorem solution (lifetime t : ℝ) (ht : lifetime < t) : bcAlive lifetime t = 0 := by
  unfold bcAlive; rw [if_neg (not_le.mpr ht)]


