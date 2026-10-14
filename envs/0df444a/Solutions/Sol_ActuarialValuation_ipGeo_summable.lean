-- Prove2me | solution 1 for ActuarialValuation.ipGeo_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:24:14.220175+00:00
-- url     : https://prove2.me/submissions/074ea7b4-4605-43b2-bed8-120b5d05c19d

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_actuarial_ipGeo

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (ipGeo q) := by
  have hnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  change Summable (fun n : ℕ => (1-q)*q^n)
  exact (summable_geometric_of_norm_lt_one hnorm).mul_left (1-q)
