-- Prove2me | solution 1 for ActuarialValuation.ipGeo_normalized
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:27:43.029163+00:00
-- url     : https://prove2.me/submissions/33015e15-cb91-4402-8ae6-7b40ef5e941d

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_ipGeo

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n : ℕ, ipGeo q n) = 1 := by
  have hnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  change (∑' n : ℕ, (1-q)*q^n) = 1
  rw [tsum_mul_left]
  rw [tsum_geometric_of_norm_lt_one hnorm]
  have hden : 1-q ≠ 0 := by linarith
  field_simp
