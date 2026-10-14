-- Prove2me | solution 1 for ActuarialValuation.kmGreenwoodSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:16:20.571195+00:00
-- url     : https://prove2.me/submissions/7c635c93-5001-497b-9da3-b7f554d02eda

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmGreenwoodTerm
import Definitions.Def_actuarial_kmGreenwoodSum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r d : ℕ → ℝ) (n : ℕ) :
    kmGreenwoodSum r d (n+1) =
      kmGreenwoodSum r d n + kmGreenwoodTerm (d n) (r n) := by
  simp [kmGreenwoodSum, Finset.sum_range_succ]
