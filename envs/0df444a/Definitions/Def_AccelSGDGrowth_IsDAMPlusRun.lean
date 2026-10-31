-- Prove2me | Definitions.Def_AccelSGDGrowth_IsDAMPlusRun
-- name    : AccelSGDGrowth_IsDAMPlusRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:26.908541+00:00
-- url     : https://prove2.me/theorems/2f47b60b-df7e-4a1a-92f0-b8515bdb75ea
-- title:
--   A run of DAM+ (4.6)
-- statement:
--   Let $m\in\mathbb R$, weights $(a_k)$, step sizes $(\eta_k)$, and sequences $x_k,y_k,z_k,g_k\in\mathbb R^d$. They form a **run of DAM+** if for every $k\ge1$
--   $$
--   x_k=\frac{A_{k-1}}{A_k}\,y_k+\frac{a_k}{A_k}\,\nabla\phi_k^\star(z_k),\qquad z_{k+1}=z_k-a_kg_k,\qquad y_{k+1}=x_k-\eta_kg_k ,
--   $$
--   where $A_k=\sum_{i\le k}a_i$ and $\phi_k^\star$ is the conjugate of $\phi_k$ built from $x_1,\dots,x_k$. The point $x_k$ is a convex combination of the SGD iterate $y_k$ and the dual-averaging iterate $\nabla\phi_k^\star(z_k)$; the gradient $g_k$ is queried at $x_k$.
--
--   Since $\phi_k$ contains $x_k$, the first equation is implicit in $x_k$.
--
--   **Formalization Note** A run is a family of sequences satisfying the equations, not a recursive definition: for $k\ge2$ the implicit equation has exactly one solution, and at $k=1$ it forces $z_1=0$ (milestone (4.7)). The gradients $g_k$ are arbitrary here; their law is imposed by the growth condition. Indices start at 1.
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, (4.6a)–(4.6c), p.16

import Definitions.Def_AccelSGDGrowth_cumWeight
import Definitions.Def_AccelSGDGrowth_phiStar

namespace AccelSGDGrowth

/-- A run of DAM+ (Chen, Na, Kolar, arXiv:2006.06782v4, (4.6), p.16): sequences of iterates `x`,
`y`, dual variables `z` and (stochastic) gradients `g` in `ℝ^d` such that for every `k ≥ 1`
* (4.6a) `x_k = (A_{k-1}/A_k) y_k + (a_k/A_k) ∇φ⋆_k(z_k)`,
* (4.6b) `z_{k+1} = z_k - a_k g_k`,
* (4.6c) `y_{k+1} = x_k - η_k g_k`,
where `A_k = cumWeight a k` and `φ⋆_k = phiStar m a x k` is built from `x_1, …, x_k`.

**Formalization Note.** Indices start at 1, index 0 unused. Since `φ_k` contains `x_k`, (4.6a) is an
implicit equation for `x_k`; a run is any family of sequences satisfying the equations, not a
recursive definition (milestone (4.7) shows the equation has exactly one solution for `k ≥ 2`, and at
`k = 1` it forces `z_1 = 0`). The gradients `g k` are arbitrary vectors here; their law is imposed
separately by the growth condition. `y_1` enters only with coefficient `A_0/A_1 = 0`. -/
def IsDAMPlusRun {d : ℕ} (m : ℝ) (a η : ℕ → ℝ) (x y z g : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    x k = (cumWeight a (k - 1) / cumWeight a k) • y k +
      (a k / cumWeight a k) • gradient (phiStar m a x k) (z k) ∧
    z (k + 1) = z k - a k • g k ∧
    y (k + 1) = x k - η k • g k

end AccelSGDGrowth


