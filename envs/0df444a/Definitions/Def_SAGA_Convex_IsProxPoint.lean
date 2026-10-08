-- Prove2me | Definitions.Def_SAGA_Convex_IsProxPoint
-- name    : SAGA_Convex_IsProxPoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:11:10.427926+00:00
-- url     : https://prove2.me/theorems/5abeddba-8e8c-406a-9052-57636b7b71d0
-- title:
--   Proximal point: $p=\mathrm{prox}_\gamma^h(y)$
-- statement:
--   Let $h:\mathbb R^d\to\mathbb R$ and $\gamma\in\mathbb R$. A point $p$ is a **proximal point** of $y$ (for $h$ with parameter $\gamma$) when it minimizes the proximal objective:
--
--   $$
--   h(p)+\frac1{2\gamma}\|p-y\|^2\le h(z)+\frac1{2\gamma}\|z-y\|^2\qquad\text{for all } z\in\mathbb R^d .
--   $$
--
--   For convex $h$ and $\gamma>0$ the minimizer exists and is unique, and it is the proximal operator $\mathrm{prox}_\gamma^h(y)=\arg\min_x\{h(x)+\frac1{2\gamma}\|x-y\|^2\}$ of the paper's eq. (3). The SAGA iteration applies this operator after each gradient step.
--
--   **Formalization Note** The proximal operator is not defined by a choice function: the theorems take a map $P$ with $P(y)$ a proximal point of $y$ for every $y$. For convex real-valued $h$ and $\gamma>0$ such a $P$ is unique and equals $\mathrm{prox}_\gamma^h$.
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, p. 2, eq. (3)

import Mathlib

namespace SAGA.Convex

/-- `p` is a minimizer of `h(z) + (1/(2γ)) ‖z - y‖²` over `z`, i.e. `p = prox_γ^h(y)`
(Defazio–Bach–Lacoste-Julien, p. 2, eq. (3)). -/
def IsProxPoint {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → ℝ) (γ : ℝ)
    (y p : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ z : EuclideanSpace ℝ (Fin d),
    h p + 1 / (2 * γ) * ‖p - y‖ ^ 2 ≤ h z + 1 / (2 * γ) * ‖z - y‖ ^ 2

end SAGA.Convex


