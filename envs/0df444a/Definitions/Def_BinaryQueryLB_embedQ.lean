-- Prove2me | Definitions.Def_BinaryQueryLB_embedQ
-- name    : BinaryQueryLB_embedQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:09.328852+00:00
-- url     : https://prove2.me/theorems/8759ef09-40cc-4a41-adac-b3263380748c
-- title:
--   The vector $(\gamma,0)\in\mathbb R^d$
-- statement:
--   Let $m=\lfloor d/2\rfloor$. For $\gamma=(\gamma_x,\gamma_z)\in\mathbb R^{2m}$, the vector $(\gamma,0)\in\mathbb R^d$ has $\gamma_x$ in its first $m$ coordinates, $\gamma_z$ in the next $m$, and $0$ in the remaining $d-2m$ coordinates (the zero block). It is the transpose of the map $y\mapsto\bar y$.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §2.3, p.12

import Mathlib
import Definitions.Def_BinaryQueryLB_PtSpace

namespace BinaryQueryLB

/-- **The vector `(γ, 0) ∈ ℝ^d` with `d − 2m` coordinates in the zero block.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §2.3, p.12:
"`g_W(y) = (M/2)(v_{i_W(y)}(W) + r_rad(q), 0) ∈ R^d`, with `d − 2m` coordinates in the zero block".

`embedQ d γ` has coordinates `γ_x` in positions `0, …, m − 1`, `γ_z` in positions `m, …, 2m − 1`,
and `0` in the remaining `d − 2m` positions (`m = d / 2`). It is the transpose of `ybar`. -/
noncomputable def embedQ (d : ℕ) (γ : PtSpace (d / 2)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun k : Fin d =>
    if h : k.1 < d / 2 then γ (Sum.inl ⟨k.1, h⟩)
    else if h' : k.1 < 2 * (d / 2) then γ (Sum.inr ⟨k.1 - d / 2, by omega⟩) else 0)

end BinaryQueryLB


