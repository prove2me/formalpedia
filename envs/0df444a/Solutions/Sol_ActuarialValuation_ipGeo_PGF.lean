-- Prove2me | solution 1 for ActuarialValuation.ipGeo_PGF
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:33:10.309287+00:00
-- url     : https://prove2.me/submissions/56fbb651-f18f-4c94-9082-61c01cbc6bd4

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_ipGeo
import Definitions.Def_actuarial_ipCountPGF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (q z : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ipCountPGF (ipGeo q) z = (1-q)/(1-q*z) := by
  have hprod : q*z ≤ q := by
    calc
      q*z ≤ q*1 := mul_le_mul_of_nonneg_left hz1 hq0
      _ = q := by ring
  have hnorm : ‖q*z‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hq0 hz0)]
    exact lt_of_le_of_lt hprod hq1
  calc
    ipCountPGF (ipGeo q) z = ∑' n : ℕ, (1-q)*(q*z)^n := by
      unfold ipCountPGF
      apply tsum_congr
      intro n
      dsimp [ipGeo]
      rw [mul_pow]
      ring
    _ = (1-q)*(∑' n : ℕ, (q*z)^n) := by
      rw [tsum_mul_left]
    _ = (1-q)/(1-q*z) := by
      rw [tsum_geometric_of_norm_lt_one hnorm]
      rw [div_eq_mul_inv]
