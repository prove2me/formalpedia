-- Prove2me | solution 1 for ActuarialValuation.ipPoiRHS_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:23:44.551503+00:00
-- url     : https://prove2.me/submissions/6a7ec004-31a8-4e81-a02b-54e41e517f7c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipPoiRHS
open ActuarialValuation

theorem solution(l : ℝ) (f g : ℕ → ℝ) : ipPoiRHS l f g 1=l*f 1*g 0 := by
  simp [ipPoiRHS]
  ring
