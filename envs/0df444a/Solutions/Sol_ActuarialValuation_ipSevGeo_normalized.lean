-- Prove2me | solution 1 for ActuarialValuation.ipSevGeo_normalized
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:49:56.840576+00:00
-- url     : https://prove2.me/submissions/148b1761-e856-4bdb-8f68-fa1e6e7ac904

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_ipSevGeo

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' k : ℕ, ipSevGeo r k) = 1 := by
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  change (∑' k : ℕ, (1-r)*r^k) = 1
  rw [tsum_mul_left]
  rw [tsum_geometric_of_norm_lt_one hnorm]
  have hden : 1-r ≠ 0 := by linarith
  field_simp
