-- Prove2me | Definitions.Def_ShapleyNV_inCost
-- name    : ShapleyNV_inCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:52:03.814049+00:00
-- url     : https://prove2.me/theorems/b12da188-858b-4709-82f7-736b59e9b66e
-- title:
--   Transport cost on $\widehat{\mathcal X}\times\mathcal Z$
-- statement:
--   On the in-sample space $\widehat{\mathcal X} \times \mathcal Z$ the ground cost is the restriction of the cost $\|x-x'\| + |z-z'|$:
--
--   $$
--   c\big((\hat x_k, z), (\hat x_{k'}, z')\big) := \|\hat x_k - \hat x_{k'}\| + |z - z'| .
--   $$
--
--   **Formalization Note** Points of $\widehat{\mathcal X}$ are written by their index $k$; the cost is the sum of the two distances.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), §2.2, eq. (3), p.5, on 𝒳̂ × 𝒵 as in (P̂), p.6

import Mathlib
import Definitions.Def_ShapleyNV_Data

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Transport cost on `𝒳̂ × 𝒵`**: `c((k, z), (k', z')) := ‖x̂_k − x̂_k'‖ + |z − z'|`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), §2.2, eq. (3), p.5, restricted to the in-sample feature set `𝒳̂` used in (P̂), p.6.

**Formalization Note.** `𝒳̂` is `Fin K` through `k ↦ x̂_k`; the cost is the sum of the feature
distance `dist (x̂_k) (x̂_k')` and the demand distance `|z − z'|` (not Lean's max metric). -/
def inCost {X : Type*} [MetricSpace X] (D : Data X) (p q : Fin D.K × ℝ≥0) : ℝ :=
  dist (D.xhat p.1) (D.xhat q.1) + dist p.2 q.2

end ShapleyNV


