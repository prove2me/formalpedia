-- Prove2me | Definitions.Def_BiconvexProg_Boundary_eucDist
-- name    : BiconvexProg_Boundary_eucDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T17:48:18.863989+00:00
-- url     : https://prove2.me/theorems/550743e4-bf91-4d63-afa8-cbc123b519b5
-- title:
--   Euclidean distance on $\mathbb{R}^p \times \mathbb{R}^q$
-- statement:
--   For points $z = (x, y)$ and $w = (x', y')$ of $\mathbb{R}^p \times \mathbb{R}^q$, the **Euclidean distance** is
--
--   $$d(z, w) = \sqrt{\|x - x'\|_2^2 + \|y - y'\|_2^2},$$
--
--   where $\|\cdot\|_2$ is the Euclidean norm on each block. This is the distance of $\mathbb{R}^{p+q}$ under the identification $\mathbb{R}^p \times \mathbb{R}^q = \mathbb{R}^{p+q}$.
--
--   It is the distance used in the proof of Theorem 1 of Al-Khayyal and Falk ("a point on $\partial S$ which minimizes the Euclidean distance between $\partial S$ and $(\bar x, \bar y)$").
--
--   **Formalization Note** Mathlib's default metric on a product type is the maximum of the block distances, so the Euclidean distance on the product is written out explicitly.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, p. 274, Proof of Theorem 1 ('minimizes the Euclidean distance')

import Mathlib

namespace BiconvexProg.Boundary

/-- The Euclidean distance on `ℝᵖ × ℝ^q`:
`eucDist (x, y) (x', y') = √(‖x - x'‖² + ‖y - y'‖²)`. (Mathlib's default metric on a product
type is the sup metric, so the Euclidean one is written out.) -/
noncomputable def eucDist {p q : ℕ}
    (z w : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) : ℝ :=
  Real.sqrt (‖z.1 - w.1‖ ^ 2 + ‖z.2 - w.2‖ ^ 2)

end BiconvexProg.Boundary


