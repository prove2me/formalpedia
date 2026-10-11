-- Prove2me | solution 1 for ActuarialValuation.ipGeoRHS_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:24:45.140931+00:00
-- url     : https://prove2.me/submissions/df2d6381-7311-4b31-8220-d5d7e0b3b5e4

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipGeoRHS
open ActuarialValuation

theorem solution(q : ℝ) (f g : ℕ → ℝ) : ipGeoRHS q f g 1=q*f 1*g 0 := by
  simp [ipGeoRHS]
  ring
