-- Prove2me | Definitions.Def_BinaryQueryLB_Chart
-- name    : BinaryQueryLB_Chart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:54.440576+00:00
-- url     : https://prove2.me/theorems/cf9a4b74-fcb2-4102-82f5-abd78a8a958b
-- title:
--   The type of first-order charts
-- statement:
--   A first-order chart is a map $G$ that assigns a vector $G(f,y)\in\mathbb R^d$ to a function $f:\mathbb R^d\to\mathbb R$ and a point $y\in\mathbb R^d$. The subgradient requirement is imposed separately (first-order chart, Definition 2.2).
--
--   **Formalization Note** A total map; only its values at $f\in F(d,R,M)$ and $y\in X$ matter.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.2, p.11

import Mathlib

namespace BinaryQueryLB

/-- **The type of first-order charts.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.2, p.11: a chart assigns a vector
`G(f, y)` to a function `f` and a point `y`.

**Formalization Note.** A chart is a total map `(ℝ^d → ℝ) → ℝ^d → ℝ^d`; only its values at
`f ∈ F(d, R, M)` and `y ∈ X` matter, and the subgradient requirement is `IsChart`. -/
abbrev Chart (d : ℕ) : Type :=
  (EuclideanSpace ℝ (Fin d) → ℝ) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)

end BinaryQueryLB


