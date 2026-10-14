-- Prove2me | solution 1 for ActuarialValuation.ipCompound_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:12:37.292891+00:00
-- url     : https://prove2.me/submissions/4211ccc1-781e-4052-bb5a-c0a5fd77494f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipCompound
import Definitions.Def_actuarial_ipCountPGF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p f : ℕ → ℝ)
    (hs : Summable (fun n : ℕ => p n * (f 0)^n)) :
    ipCompound p f 0 = ipCountPGF p (f 0) := by
  have hfold : ∀ n : ℕ, ipFold f n 0 = (f 0)^n := by
    intro n
    induction n with
    | zero =>
      change ipPoint 0 = (f 0)^0
      simp [ipPoint]
    | succ n ih =>
      change ipConvolve f (ipFold f n) 0 = (f 0)^(n+1)
      simp [ipConvolve, ih, pow_succ, mul_comm]
  unfold ipCompound ipCountPGF
  exact tsum_congr (fun n => congrArg (fun v : ℝ => p n * v) (hfold n))
