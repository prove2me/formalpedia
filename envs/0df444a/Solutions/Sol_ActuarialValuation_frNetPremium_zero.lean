-- Prove2me | solution 1 for ActuarialValuation.frNetPremium_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:43:52.348158+00:00
-- url     : https://prove2.me/submissions/76130bc2-fb3d-46d6-bbe5-e9f318cd48c1

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frNetPremium
open ActuarialValuation

theorem solution(annuityPV : ℝ) : frNetPremium 0 annuityPV = 0 := by
  simp [frNetPremium]
