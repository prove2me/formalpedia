-- Prove2me | Definitions.Def_SAGA_StronglyConvex_IsProxPoint
-- name    : SAGA_StronglyConvex_IsProxPoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:53:46.671733+00:00
-- url     : https://prove2.me/theorems/f651480f-dfc8-40e1-9af7-09ee08492769
-- title:
--   Proximal point: $p$ minimizes $h(x)+\frac{1}{2\gamma}\|x-y\|^2$
-- statement:
--   Let $E$ be a real inner product space, $h:E\to\mathbb R$ a function, $\gamma\in\mathbb R$ and $y,p\in E$. We say that $p$ is a **proximal point** of $h$ with parameter $\gamma$ at $y$ if $p$ minimizes the objective of the proximal problem, that is, for every $z\in E$,
--
--   $$
--   h(p)+\frac{1}{2\gamma}\|p-y\|^2\;\le\;h(z)+\frac{1}{2\gamma}\|z-y\|^2 .
--   $$
--
--   In other words, $p\in\operatorname{argmin}_{x}\{h(x)+\frac{1}{2\gamma}\|x-y\|^2\}$, which is the defining property of the proximal operator $\operatorname{prox}^h_\gamma(y)$ of Defazio, Bach and Lacoste-Julien, eq. (3). When $h$ is convex and $\gamma>0$ the objective is strongly convex and continuous, so the minimizer exists and is unique; a map $P$ with $P(y)$ a proximal point at every $y$ is then exactly $\operatorname{prox}^h_\gamma$.
--
--   This predicate is how every theorem of the mission says "$P$ is the proximal operator used by SAGA".
--
--   **Formalization Note** The predicate is stated for an arbitrary real-valued $h$ and real $\gamma$; convexity of $h$ and the value of $\gamma>0$ are hypotheses of the theorems that use it. Extended-valued $h$ (indicator functions of constraint sets) is outside the scope, as in the paper, which types $h$ as a finite function on $\mathbb R^d$.
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, p. 2, eq. (3)

import Mathlib

namespace SAGA.StronglyConvex

/-- `IsProxPoint h γ y p`: the point `p` minimizes `x ↦ h x + 1/(2γ) ‖x - y‖²`, i.e.
`p` is a value of the proximal operator `prox_γ^h (y)` of Defazio–Bach–Lacoste-Julien (2014),
eq. (3), p. 2. -/
def IsProxPoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h : E → ℝ) (γ : ℝ) (y p : E) : Prop :=
  ∀ z : E, h p + 1 / (2 * γ) * ‖p - y‖ ^ 2 ≤ h z + 1 / (2 * γ) * ‖z - y‖ ^ 2

end SAGA.StronglyConvex


