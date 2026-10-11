-- Prove2me | solution 1 for ActuarialValuation.pfAmortisation_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:16:10.270128+00:00
-- url     : https://prove2.me/submissions/1248a081-e9b2-4d2d-9e10-d4c064b2df2f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAmortisation
open ActuarialValuation

theorem solution(annuity : ℝ) : pfAmortisation 0 annuity=0 := by
  simp [pfAmortisation]
