-- Prove2me | solution 1 for ActuarialAnnuitiesContinuous.bc_guarantee_entitlement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:09:09.724709+00:00
-- url     : https://prove2.me/submissions/56577421-62f9-4642-b75b-f9a68c975c16

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcAlive
import Definitions.Def_actuarial_bcEntitled

open ActuarialAnnuitiesContinuous

open MeasureTheory

theorem solution (a g t lifetime : ℝ) (ht : t < a+g) : bcEntitled a g t lifetime = bcAlive lifetime a := by
  unfold bcEntitled; rw [if_pos ht]


