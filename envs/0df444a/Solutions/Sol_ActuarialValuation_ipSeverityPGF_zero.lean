-- Prove2me | solution 1 for ActuarialValuation.ipSeverityPGF_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:49:19.110636+00:00
-- url     : https://prove2.me/submissions/b9d8b7c4-57ba-4075-9d4a-cd76fc8be16a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipSeverityPGF
open ActuarialValuation

theorem solution(f : ℕ → ℝ) : ipSeverityPGF f 0=f 0 := by
  unfold ipSeverityPGF
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]
