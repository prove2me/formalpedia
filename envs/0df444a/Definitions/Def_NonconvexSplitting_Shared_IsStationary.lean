-- Prove2me | Definitions.Def_NonconvexSplitting_Shared_IsStationary
-- name    : NonconvexSplitting_Shared_IsStationary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T12:41:12.969061+00:00
-- url     : https://prove2.me/theorems/97afe5b6-79d2-4007-8a71-03eb93abbdac
-- title:
--   Stationary point of $\min_x h(x) + P(\mathcal M x)$
-- statement:
--   Let $h : \mathbb{R}^n \to \mathbb{R}$ be differentiable, $P : \mathbb{R}^m \to (-\infty, +\infty]$, and $\mathcal M : \mathbb{R}^n \to \mathbb{R}^m$ linear with adjoint $\mathcal M^*$. A point $x$ is a **stationary point** of the problem $\min_x h(x) + P(\mathcal M x)$ if
--   $$
--   0 \in \nabla h(x) + \mathcal M^* \partial P(\mathcal M x),
--   $$
--   that is, there is $w \in \partial P(\mathcal M x)$ with $\nabla h(x) + \mathcal M^* w = 0$, where $\partial P$ is the limiting subdifferential.
--
--   This is condition (4) of the paper, which every local minimizer satisfies when $\mathcal M$ is surjective; the paper takes it as the definition of stationarity.
--
--   **Formalization Note** The definition is the inclusion (4) itself, not $0 \in \partial(h + P\circ\mathcal M)(x)$; the two agree under the paper's hypotheses by a calculus rule that is not part of this definition.
--
--   **Shared definition.** Serves chunks `01-admm-stationary` (p. 4, Eq. (4) and the sentence after it; previously `NonconvexSplitting.ProxADMM.IsStationary`) and `03-admm-kl-convergence` (p. 4, Eq. (4) and the sentence after it; previously `NonconvexSplitting.ADMMKL.IsStationary`). Every copy had the same Lean body, identical up to the namespace, and the same conventions; it is reviewed once here for all of them.
-- source:
--   Li & Pong, Global Convergence of Splitting Methods for Nonconvex Composite Optimization, arXiv:1407.0753v6, p. 4, Eq. (4) and the sentence after it; shared by chunks 01-admm-stationary, 03-admm-kl-convergence

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff

namespace NonconvexSplitting.Shared

/-- Stationarity (4) of Li–Pong (p. 4) for problem (1), `min_x h(x) + P(M x)`:
`x` is stationary iff `0 ∈ ∇h(x) + M* ∂P(M x)`, i.e. there is `w ∈ ∂P(M x)` (limiting
subdifferential (2)) with `∇h(x) + M* w = 0`. -/
def IsStationary {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin m) → EReal)
    (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ w ∈ LimitingSubdiff P (M x), gradient h x + ContinuousLinearMap.adjoint M w = 0

end NonconvexSplitting.Shared


