-- Prove2me | solution 1 for ActuarialValuation.clBFUltimate_zero_prior
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:36:39.317392+00:00
-- url     : https://prove2.me/submissions/e02345b5-fb59-43de-b598-2898d672ff0d

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clBFUltimate
open ActuarialValuation

theorem solution(c f : ℝ) : clBFUltimate c 0 f = c := by
  simp [clBFUltimate, clBFReserve]
