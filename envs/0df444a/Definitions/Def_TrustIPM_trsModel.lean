-- Prove2me | Definitions.Def_TrustIPM_trsModel
-- name    : TrustIPM_trsModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:09.683197+00:00
-- url     : https://prove2.me/theorems/a831df69-83f1-4c1f-ab4b-7c3e00dbe026
-- title:
--   Lemma 8 — the trust-region model $\Delta(u)=\tfrac12u^THu+g^Tu$ and its value $\sigma(r)$
-- statement:
--   For a linear map $H:\mathbb R^n\to\mathbb R^n$ and $g\in\mathbb R^n$, the **trust-region model** is
--
--   $$
--   \Delta(u):=\tfrac12\,u^THu+g^Tu ,
--   $$
--
--   and the **value of the trust-region subproblem** of radius $r$ is
--
--   $$
--   \sigma(r):=\min_{u\in B_r(0)}\Delta(u),\qquad B_r(0)=\{u\in\mathbb R^n:\|u\|_2\le r\}.
--   $$
--
--   The search direction of the interior point method is a minimizer of this model with $H=\nabla^2\psi_\mu(x)$ and $g=\nabla\psi_\mu(x)$; Lemmas 8 and 9 are statements about $\Delta$ and $\sigma$.
--
--   **Formalization Note** $u^THu$ is the inner product $\langle Hu,u\rangle$ in `EuclideanSpace ℝ (Fin n)`. The minimum is the infimum of the image of the closed ball, which is attained for $r\ge0$; for $r<0$ the ball is empty and the value is Lean's default $0$, and no statement uses it there.
-- source:
--   Hinder & Ye, Worst-case iteration bounds for log barrier methods on problems with nonconvex constraints, arXiv:1807.00404v5, Lemma 8, p.13; model M^ψµ_x, p.3

import Mathlib
open scoped InnerProductSpace RealInnerProductSpace

namespace TrustIPM

/-- The **trust-region model** `Δ(u) := ½ uᵀHu + gᵀu` (Hinder & Ye, *Worst-case iteration bounds for
log barrier methods on problems with nonconvex constraints*, arXiv:1807.00404v5, Lemma 8, p.13; the
same quadratic is `M^{ψµ}_x` on p.3 with `H = ∇²ψµ(x)`, `g = ∇ψµ(x)`).

**Formalization Note** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`, the matrix `H` is a continuous linear map
`ℝⁿ → ℝⁿ`, and `uᵀHu = ⟪H u, u⟫`, `gᵀu = ⟪g, u⟫`. -/
noncomputable def trsModel {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 / 2 : ℝ) * ⟪H u, u⟫_ℝ + ⟪g, u⟫_ℝ

/-- The **optimal value of the trust-region subproblem** `σ(r) := min_{u ∈ B_r(0)} Δ(u)` (Hinder & Ye,
arXiv:1807.00404v5, Lemma 8, p.13), with `B_r(0) := {u ∈ ℝⁿ : ‖u‖₂ ≤ r}` (p.3).

**Formalization Note** The minimum is `sInf` of the image of the closed Euclidean ball. For `r ≥ 0`
the ball is compact and nonempty and `Δ` is continuous, so the infimum is attained and equals the
paper's minimum. For `r < 0` the ball is empty and the value is Lean's junk `0`; every statement about
`σ` restricts to `r ≥ 0`, as the paper does. -/
noncomputable def trsValue {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (r : ℝ) : ℝ :=
  sInf (trsModel H g '' Metric.closedBall 0 r)

end TrustIPM


