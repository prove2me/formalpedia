-- Prove2me | Definitions.Def_BinaryQueryLB_ybar
-- name    : BinaryQueryLB_ybar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:10.795604+00:00
-- url     : https://prove2.me/theorems/bad6c877-0e04-46c1-bca4-07cf2cafea3e
-- title:
--   The first $2m$ coordinates $\bar y$ of $y\in\mathbb R^d$
-- statement:
--   Let $m=\lfloor d/2\rfloor$. For $y\in\mathbb R^d$, $\bar y\in\mathbb R^{2m}$ is the vector of its first $2m$ coordinates, split as $\bar y=(x,z)$ with $x=(y_1,\dots,y_m)$ and $z=(y_{m+1},\dots,y_{2m})$. When $d$ is odd, the last coordinate of $y$ is ignored.
--
--   **Formalization Note** Coordinates are indexed from $0$: $x_i=y_i$ and $z_j=y_{m+j}$ for $0\le i,j<m$.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.4, p.12

import Mathlib
import Definitions.Def_VRAccelCLT_stack
import Definitions.Def_BinaryQueryLB_PtSpace

namespace BinaryQueryLB

/-- **The first `2m` coordinates `ȳ` of `y ∈ ℝ^d`.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.4, p.12: "For `y ∈ R^d` let
`ȳ ∈ R^{2m}` be its first `2m` coordinates", with `m = ⌊d/2⌋`.

`ybar d y = (x, z)` with `x_i = y_i` and `z_j = y_{m+j}` (indices from `0`, `m = d / 2`). When
`d` is odd, the last coordinate of `y` is ignored.

**Formalization Note.** The pair `(x, z)` is the platform's `VRAccelCLT.stack` (first block
`Sum.inl`). -/
noncomputable def ybar (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) : PtSpace (d / 2) :=
  VRAccelCLT.stack (WithLp.toLp 2 fun i => y ⟨i.1, by have := i.2; omega⟩)
    (WithLp.toLp 2 fun j => y ⟨d / 2 + j.1, by have := j.2; omega⟩)

end BinaryQueryLB


