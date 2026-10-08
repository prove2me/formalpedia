-- Prove2me | Definitions.Def_ProjLikeRetr_Retractor_retractorR
-- name    : ProjLikeRetr_Retractor_retractorR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:45:44.504372+00:00
-- url     : https://prove2.me/theorems/89b23d41-c63b-4a89-b094-4709dd030d92
-- title:
--   Theorem 4.2, pp. 15–16 — the point-to-set map R(x,u): points of M ∩ (x+u+D(x,u)) nearest to x+u
-- statement:
--   Let $\mathcal M$ be a subset of a Euclidean space $\mathcal E$ and let $D$ assign to each $(x,u)\in\mathcal E\times\mathcal E$ a linear subspace $D(x,u)$ of $\mathcal E$. Define the affine space $\mathcal D(x,u)=x+u+D(x,u)$ and
--
--   $$R(x,u)=\Bigl\{z\in\mathcal M\cap\mathcal D(x,u):\ \|x+u-z\|\le\|x+u-w\|\ \text{ for all } w\in\mathcal M\cap\mathcal D(x,u)\Bigr\},$$
--
--   the set of points of $\mathcal M\cap\mathcal D(x,u)$ nearest to $x+u$. When $D$ is a retractor, this is the point-to-set map of Theorem 4.2, the **retraction induced by the retractor $D$**: from $x+u$ one comes back to $\mathcal M$ along the admissible directions $D(x,u)$, choosing the smallest restoration step.
--
--   **Formalization Note** $R(x,u)$ is a set (possibly empty, possibly with several points); "nearest point" is the published predicate `RandomGradFree.Nonsmooth.IsMetricProjection` applied to the set $\mathcal M\cap\mathcal D(x,u)$ and the point $x+u$.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, pp. 15–16, Theorem 4.2 (definition of R)

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection

namespace ProjLikeRetr.Retractor

/-- Theorem 4.2, pp. 15–16: the point-to-set map `R` induced by `D`: `R(x, u)` is the set of
points of `M ∩ 𝒟(x, u)` nearest to `x + u`, where `𝒟(x, u) = x + u + D(x, u)` is the affine
space through `x + u` directed by `D(x, u)`. -/
def retractorR {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : Set E) (D : E × E → Submodule ℝ E) (p : E × E) : Set E :=
  {z | RandomGradFree.Nonsmooth.IsMetricProjection
    (M ∩ {y | ∃ w ∈ D p, y = p.1 + p.2 + w}) (p.1 + p.2) z}

end ProjLikeRetr.Retractor


