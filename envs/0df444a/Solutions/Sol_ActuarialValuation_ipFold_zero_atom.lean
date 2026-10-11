-- Prove2me | solution 1 for ActuarialValuation.ipFold_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:43:21.150757+00:00
-- url     : https://prove2.me/submissions/bda7936e-2e0e-4173-add9-1e229c2fba4c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipFold
open ActuarialValuation

theorem solution(f : ℕ → ℝ) (n : ℕ) : ipFold f n 0=(f 0)^n := by
  induction n with
  | zero => simp [ipFold, ipPoint]
  | succ n ih =>
    show ipConvolve f (ipFold f n) 0 = f 0 ^ (n + 1)
    simp [ipConvolve, ih, pow_succ, mul_comm]
