-- Prove2me | Definitions.Def_ShapleyNV_fullCost
-- name    : ShapleyNV_fullCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:04.56208+00:00
-- url     : https://prove2.me/theorems/1f24e687-71f9-4070-ae4a-d46632a0760c
-- title:
--   Transport cost $\|x-x'\|+|z-z'|$ on $\mathcal X\times\mathcal Z$
-- statement:
--   The ground cost of the Wasserstein distance on feature–demand pairs is
--
--   $$
--   c\big((x, z), (x', z')\big) := \|x - x'\| + |z - z'| ,
--   $$
--
--   the **sum** of the feature distance and the demand distance.
--
--   **Formalization Note** The feature space is a metric space and $\|x - x'\|$ is its distance. The sum is written out: the default distance on a product of metric spaces in Lean is the maximum of the two distances, which is not the paper's cost.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), §2.2, eq. (3), p.5

import Mathlib

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Transport cost on `𝒳 × 𝒵`**: `c((x, z), (x', z')) := ‖x − x'‖ + |z − z'|`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), §2.2, eq. (3), p.5 (the integrand of the Wasserstein distance).

**Formalization Note.** The feature space is a metric space and `‖x − x'‖` is `dist x x'`
(the paper's `𝒳 ⊂ (ℝ^d, ‖·‖)` with `dist x x' = ‖x − x'‖` is an instance). The cost is the
**sum** of the two distances, written out explicitly: Lean's own metric on a product is the max,
which is not the paper's cost. -/
def fullCost {X : Type*} [MetricSpace X] (p q : X × ℝ≥0) : ℝ := dist p.1 q.1 + dist p.2 q.2

end ShapleyNV


