-- Prove2me | solution 1 for ActuarialValuation.ipCountPGF_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:11:26.823918+00:00
-- url     : https://prove2.me/submissions/56a64b5e-fa49-42d0-9d5f-ffcdf714600b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipCountPGF
open ActuarialValuation

theorem solution(p : ℕ → ℝ) : ipCountPGF p 0=p 0 := by
  unfold ipCountPGF
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]
