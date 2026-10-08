-- Prove2me | Definitions.Def_weightedRootKeyholeIntegrand
-- name    : weightedRootKeyholeIntegrand
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-09-16T13:12:43.233723+00:00
-- url     : https://prove2.me/theorems/8bcb9b2b-6c80-4aac-923f-63a59cf70edd
-- title:
--   Weighted-root keyhole contour integrand
-- statement:
--   We define the weighted-root contour integrand and its line integral along the assembled keyhole boundary. These concrete objects instantiate the abstract contour-assembly infrastructure for the weighted geometric-mean proof.
-- source:
--   Principal weighted-root keyhole integrand used in the contour representation of the weighted geometric mean.

import Mathlib
import Definitions.Def_keyholeLineIntegral
open scoped BigOperators Interval

noncomputable def weightedRootKeyholeIntegrand (n : ℕ) (a w : ℕ → ℝ) : ℂ → ℂ := fun z =>
  (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) / z

noncomputable def weightedRootBoundaryIntegral (n : ℕ) (a w : ℕ → ℝ) (a₀ a₁ r R : ℝ) : ℂ :=
  keyholeBoundaryIntegral (weightedRootKeyholeIntegrand n a w) a₀ a₁ r R


