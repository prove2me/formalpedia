-- Prove2me | solution 1 for ActuarialValuation.ipPoi_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:37:25.178982+00:00
-- url     : https://prove2.me/submissions/8214c6a1-df4b-40e2-80c3-f0bf0cbe17d4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_ipPoisson
import Definitions.Def_actuarial_ipCompound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℝ) (f : ℕ → ℝ)
    (hf0 : 0 ≤ f 0) (hf1 : f 0 ≤ 1) :
    ipCompound (ipPoisson l) f 0 = Real.exp (-l*(1-f 0)) := by
  have hfold : ∀ n : ℕ, ipFold f n 0 = (f 0)^n := by
    intro n
    induction n with
    | zero =>
      change ipPoint 0 = (f 0)^0
      simp [ipPoint]
    | succ n ih =>
      change ipConvolve f (ipFold f n) 0 = (f 0)^(n+1)
      simp [ipConvolve, ih, pow_succ, mul_comm]
  calc
    ipCompound (ipPoisson l) f 0 =
        ∑' n : ℕ, Real.exp (-l) * ((l*f 0)^n / (Nat.factorial n : ℝ)) := by
      unfold ipCompound
      apply tsum_congr
      intro n
      dsimp [ipPoisson]
      rw [hfold n, mul_pow]
      ring
    _ = Real.exp (-l) * (∑' n : ℕ, (l*f 0)^n / (Nat.factorial n : ℝ)) := by
      rw [tsum_mul_left]
    _ = Real.exp (-l) * Real.exp (l*f 0) := by
      congr 1
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    _ = Real.exp (-l*(1-f 0)) := by
      rw [← Real.exp_add]
      congr 1
      ring
