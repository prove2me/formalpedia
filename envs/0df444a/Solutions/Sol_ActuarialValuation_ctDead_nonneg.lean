-- Prove2me | solution 1 for ActuarialValuation.ctDead_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:03:18.811853+00:00
-- url     : https://prove2.me/submissions/891c2ccc-57c0-45b1-a9cd-bfd1e53c1d08

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctDead
open ActuarialValuation

theorem solution(mu t : ℝ) (hmu : 0 ≤ mu) (ht : 0 ≤ t) : 0 ≤ ctDead mu t := by
  unfold ctDead ctAlive
  have h : Real.exp (-mu*t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  linarith
