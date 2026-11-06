-- Prove2me | Definitions.Def_BinaryQueryLB_PtSpace
-- name    : BinaryQueryLB_PtSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:55.918255+00:00
-- url     : https://prove2.me/theorems/d06446ce-fe11-42ab-99b4-8cf68f014110
-- title:
--   The space $\mathbb R^{2m}$ of points $q=(x,z)$
-- statement:
--   Points of the hard family's domain are $q=(x,z)\in\mathbb R^m\times\mathbb R^m=\mathbb R^{2m}$, with the Euclidean norm $\|q\|_2$ and the Euclidean inner product of $\mathbb R^{2m}$.
--
--   **Formalization Note** $\mathbb R^{2m}$ is `EuclideanSpace ℝ (Fin m ⊕ Fin m)`: coordinates `Sum.inl i` form $x$ and `Sum.inr j` form $z$. Its norm is the Euclidean norm, not the maximum of the two block norms.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.4, p.12

import Mathlib

namespace BinaryQueryLB

/-- **The space ℝ^{2m} of points `q = (x, z)`.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.4, p.12: "`q = (x, z) ∈ R^m × R^m`".

**Formalization Note.** ℝ^{2m} is `EuclideanSpace ℝ (Fin m ⊕ Fin m)`: coordinate `Sum.inl i` is
`x_i` and `Sum.inr j` is `z_j` (indices from `0`). Its norm `‖q‖` is the Euclidean norm `∥q∥₂` of
ℝ^{2m} and its inner product is the Euclidean one (not Mathlib's max-norm on a product). -/
abbrev PtSpace (m : ℕ) : Type := EuclideanSpace ℝ (Fin m ⊕ Fin m)

end BinaryQueryLB


