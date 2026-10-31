-- Prove2me | Definitions.Def_AccelSGDGrowth_phiStar
-- name    : AccelSGDGrowth_phiStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:28.573156+00:00
-- url     : https://prove2.me/theorems/1a8296e4-98b4-42ac-91f5-0b00537c3f91
-- title:
--   The convex conjugate $\phi_k^\star(z)=\max_x\{z^\top x-\phi_k(x)\}$
-- statement:
--   The convex conjugate (2.2) of the regularizer $\phi_k$:
--   $$
--   \phi_k^\star(z)=\max_{x\in\mathbb R^d}\big\{z^\top x-\phi_k(x)\big\}.
--   $$
--   For $k\ge1$, $m>0$ and positive weights, $\phi_k$ is a strongly convex quadratic, so the maximum is attained and $\phi_k^\star$ is a quadratic function whose gradient $\nabla\phi_k^\star$ is the dual-averaging map of DAM+ (closed form (4.7)).
--
--   **Formalization Note** Written as a real supremum. For $k=0$ the paper's $\phi_0^\star(z)$ is $+\infty$ when $z\ne0$; the real supremum returns $0$ there, and the correct value $0$ at $z=0$. The mission evaluates $\phi_0^\star$ only at $z_1=0$.
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, (2.2), p.6, applied to φ_k of (4.2), p.14

import Definitions.Def_AccelSGDGrowth_phi

namespace AccelSGDGrowth

/-- The convex conjugate $\phi_k^\star(z) = \max_u \{\langle z, u\rangle - \phi_k(u)\}$ of the regularizer
`phi` (Chen, Na, Kolar, arXiv:2006.06782v4, (2.2), p.6, applied to $\phi_k$ of (4.2), p.14).

**Formalization Note.** A real-valued supremum (`⨆`). For `k ≥ 1`, positive weights and `m > 0`,
`phi` is a strongly convex quadratic, so the supremum is finite and attained (milestone (4.7)) and the
conjugate is a quadratic function of `z`; its `gradient` is the paper's $\nabla\phi_k^\star$. For
`k = 0`, `phi = 0` and the paper's $\phi_0^\star$ is `+∞` off `z = 0`; the real supremum returns the
junk value `0` there, and the correct value `0` at `z = 0`, which is the only point where the
mission evaluates $\phi_0^\star$ (at $z_1 = 0$). -/
noncomputable def phiStar {d : ℕ} (m : ℝ) (a : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d)) (k : ℕ)
    (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⨆ u : EuclideanSpace ℝ (Fin d), (inner ℝ z u - phi m a x k u)

end AccelSGDGrowth


