-- Prove2me | solution 2 for ActuarialValuation.crCreditSpread_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:41.152973+00:00
-- url     : https://prove2.me/submissions/0f0c7d0a-76a6-482a-9cb6-72b94de52a20

import Mathlib
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_crCreditSpread

open ActuarialValuation

theorem solution (face price term : ℝ) : crCreditSpread face price price term=0 := by simp [crCreditSpread]

