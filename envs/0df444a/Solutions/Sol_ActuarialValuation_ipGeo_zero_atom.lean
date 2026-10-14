-- Prove2me | solution 1 for ActuarialValuation.ipGeo_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:23:18.438875+00:00
-- url     : https://prove2.me/submissions/4af20919-1af8-4ebc-82d2-80fad6f8b2cf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_ipGeo
import Definitions.Def_actuarial_ipCompound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (q : ℝ) (f : ℕ → ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hf0 : 0 ≤ f 0) (hf1 : f 0 ≤ 1) :
    ipCompound (ipGeo q) f 0 = (1-q)/(1-q*f 0) := by
  have hfold : ∀ n : ℕ, ipFold f n 0 = (f 0)^n := by
    intro n
    induction n with
    | zero =>
      change ipPoint 0 = (f 0)^0
      simp [ipPoint]
    | succ n ih =>
      change ipConvolve f (ipFold f n) 0 = (f 0)^(n+1)
      simp [ipConvolve, ih, pow_succ, mul_comm]
  have hprod : q * f 0 ≤ q := by
    calc
      q * f 0 ≤ q * 1 := mul_le_mul_of_nonneg_left hf1 hq0
      _ = q := by ring
  have hnorm : ‖q * f 0‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hq0 hf0)]
    exact lt_of_le_of_lt hprod hq1
  calc
    ipCompound (ipGeo q) f 0 =
        ∑' n : ℕ, (1-q)*(q*f 0)^n := by
      unfold ipCompound
      apply tsum_congr
      intro n
      dsimp [ipGeo]
      rw [hfold n, mul_pow]
      ring
    _ = (1-q) * (∑' n : ℕ, (q*f 0)^n) := by
      rw [tsum_mul_left]
    _ = (1-q)/(1-q*f 0) := by
      rw [tsum_geometric_of_norm_lt_one hnorm]
      rw [div_eq_mul_inv]
