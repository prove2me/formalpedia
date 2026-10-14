-- Prove2me | solution 2 for ActuarialValuation.frReserve_start
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:33.564346+00:00
-- url     : https://prove2.me/submissions/af781dcb-324e-42d7-bb0c-a4bd8908b25b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frFractionalReserve
open ActuarialValuation

theorem solution (assets premium benefit q : ℝ) (endDiscount : ℝ) : frFractionalReserve assets premium benefit q 0 1 endDiscount = assets+premium := by
  simp [frFractionalReserve, frUddSurvival]
