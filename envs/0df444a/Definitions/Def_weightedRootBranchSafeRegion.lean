-- Prove2me | Definitions.Def_weightedRootBranchSafeRegion
-- name    : weightedRootBranchSafeRegion
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-09-18T22:21:56.946979+00:00
-- url     : https://prove2.me/theorems/5d3d39e3-b78f-48a7-82e5-7adc8c4f89b3
-- title:
--   Branch-safe annular domain for the weighted-root integrand
-- statement:
--   The branch-safe domain consists of the annulus r < |z| < R in which every shifted factor z-a_i lies in the principal-power slit plane.
-- source:
--   Common domain of the principal complex powers (z-a_i)^{w_i} and the reciprocal factor 1/z.

import Mathlib

open scoped BigOperators

def weightedRootBranchSafeRegion (n : ℕ) (a : ℕ → ℝ) (r R : ℝ) : Set ℂ :=
  {z | r < ‖z‖ ∧ ‖z‖ < R ∧ ∀ i < n, z - (a i : ℂ) ∈ Complex.slitPlane}


