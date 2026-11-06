-- Prove2me | Definitions.Def_BinaryQueryLB_LocalQuery
-- name    : BinaryQueryLB_LocalQuery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:56.880624+00:00
-- url     : https://prove2.me/theorems/f217672e-e666-4d16-87e6-1d148ff51a84
-- title:
--   Local binary query
-- statement:
--   A **local binary query** is a pair $(y,h)$ of a point $y\in\mathbb R^d$ and an arbitrary function $h:\mathbb R\times\mathbb R^d\to\{0,1\}$. No measurability or continuity of $h$ is required.
--
--   **Formalization Note** $\{0,1\}$ is `Bool`. The requirement $y\in X$ of the paper is imposed on algorithms (queries in the box).
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.3, p.11

import Mathlib

namespace BinaryQueryLB

/-- **Local binary query (Definition 2.3).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.3, p.11: "A local binary query
is a pair `(y, h)` of a point `y ∈ X` and an arbitrary function `h` from `R × R^d` to `{0, 1}`."
"No measurability or continuity of `h` is required".

**Formalization Note.** `{0, 1}` is `Bool` (`true` = 1). The requirement `y ∈ X` is imposed on
algorithms by `QueriesInBox`. -/
abbrev LocalQuery (d : ℕ) : Type :=
  EuclideanSpace ℝ (Fin d) × (ℝ × EuclideanSpace ℝ (Fin d) → Bool)

end BinaryQueryLB


