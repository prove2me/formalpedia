-- Prove2me | Definitions.Def_NonconvexSplitting_ProxGrad_IsStationary
-- name    : NonconvexSplitting_ProxGrad_IsStationary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T18:59:00.865884+00:00
-- url     : https://prove2.me/theorems/6dfdbfa3-b83a-42bc-9f32-67baf1b516d5
-- title:
--   Stationary point of $\min_x h(x) + P(x)$
-- statement:
--   Let $h : \mathbb{R}^n \to \mathbb{R}$ and $P : \mathbb{R}^n \to (-\infty, +\infty]$. A point $x$ is a **stationary point** of the problem $\min_x h(x) + P(x)$ if
--   $$
--   0 \in \nabla h(x) + \partial P(x),
--   $$
--   that is, there is $w \in \partial P(x)$ with $\nabla h(x) + w = 0$, where $\partial P$ is the limiting subdifferential.
--
--   This is the notion of stationarity (4) of the paper for problem (1) in the case where the linear map $\mathcal M$ is the identity; it is the target property of cluster points of the proximal gradient method.
--
--   **Formalization Note** Defined directly as $\exists w \in \partial P(x),\ \nabla h(x) + w = 0$ (not as $0 \in \partial(h + P)(x)$, whose equality with this set is a cited calculus rule). Since $\partial P(x)$ is empty when $P(x) = +\infty$, a stationary point lies in the domain of $P$.
-- source:
--   Li & Pong, Global Convergence of Splitting Methods for Nonconvex Composite Optimization, arXiv:1407.0753v6, p. 4, Eq. (4) with M = I (Section 4, p. 18)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
open NonconvexSplitting.Shared

namespace NonconvexSplitting.ProxGrad

/-- Stationarity (4) of Li–Pong (p. 4) for problem (1) with `M = I`, i.e. `min h(x) + P(x)`:
`x` is stationary iff `0 ∈ ∇h(x) + ∂P(x)`, with `∂` the limiting subdifferential (2). -/
def IsStationary {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin n) → EReal) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ w ∈ LimitingSubdiff P x, gradient h x + w = 0

end NonconvexSplitting.ProxGrad


