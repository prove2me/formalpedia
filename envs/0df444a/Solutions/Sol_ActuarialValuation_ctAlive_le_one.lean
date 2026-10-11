-- Prove2me | solution 1 for ActuarialValuation.ctAlive_le_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:21:01.448758+00:00
-- url     : https://prove2.me/submissions/bc34e649-d0f4-4008-a0c8-9dda8448ca1a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctAlive
open ActuarialValuation

theorem solution(mu t : ℝ) (hmu : 0 ≤ mu) (ht : 0 ≤ t) : ctAlive mu t ≤ 1 := by
  unfold ctAlive
  exact Real.exp_le_one_iff.2 (by nlinarith)
