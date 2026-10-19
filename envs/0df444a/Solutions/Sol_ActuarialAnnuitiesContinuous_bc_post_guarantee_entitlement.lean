-- Prove2me | solution 1 for ActuarialAnnuitiesContinuous.bc_post_guarantee_entitlement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:09:28.869454+00:00
-- url     : https://prove2.me/submissions/dca7426c-204b-4ab9-b65e-c596ef00d269

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

theorem solution (a g t lifetime : ℝ) (ht : a+g ≤ t) : bcEntitled a g t lifetime = bcAlive lifetime t := by
  unfold bcEntitled; rw [if_neg (not_lt.mpr ht)]


