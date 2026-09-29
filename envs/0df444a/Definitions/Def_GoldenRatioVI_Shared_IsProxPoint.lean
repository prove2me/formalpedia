-- Prove2me | Definitions.Def_GoldenRatioVI_Shared_IsProxPoint
-- name    : GoldenRatioVI_Shared_IsProxPoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:55:06.927892+00:00
-- url     : https://prove2.me/theorems/a32d11b6-5e40-4a0d-8320-79019153cbce
-- title:
--   Proximal point: $\bar x = \operatorname{prox}_g(z)$ as an argmin predicate
-- statement:
--   Let $\mathcal E$ be a real inner product space and $g:\mathcal E\to(-\infty,+\infty]$. The proximal operator of $g$ is
--   $$\operatorname{prox}_g(z) = \operatorname*{argmin}_x \Big\{ g(x) + \tfrac12\|x - z\|^2 \Big\}.$$
--   A point $\bar x$ is called a **proximal point of $g$ at $z$** if it attains this minimum, that is,
--   $$g(\bar x) + \tfrac12\|\bar x - z\|^2 \;\le\; g(x) + \tfrac12\|x - z\|^2 \qquad \text{for all } x\in\mathcal E.$$
--
--   For a proper convex lower semicontinuous $g$ the minimiser exists and is unique, so the predicate says exactly $\bar x = \operatorname{prox}_g(z)$. The Golden Ratio Algorithms apply it to $\lambda g$ with $\lambda>0$.
--
--   This definition is shared by both missions of this series: 1 (GRAAL with a fixed step: the prox step of Eq. (6), p. 4, and the prox inequality (4), p. 3, used for Theorem 1) and 2 (EGRAAL: the prox step (17) of Algorithm 1, p. 5, and the prox inequality (4), p. 3, used for Lemma 2 and Theorem 2).
--
--   **Formalization Note** The prox is stated as a predicate rather than a function, so no junk value arises; existence and uniqueness of the minimiser are theorems, not part of the definition. The comparison is carried out in `EReal`, so points with $g(x)=+\infty$ never beat a point of $\operatorname{dom} g$. The step $\operatorname{prox}_{\lambda g}$ is the predicate applied to `fun x => (λ : EReal) * g x`.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (Optimization Online 6598, 2018), p. 3, Preliminaries (definition of prox_g)

import Mathlib

namespace GoldenRatioVI.Shared

/-- `x̄` is the proximal point of `g` at `z`, i.e. `x̄ ∈ argmin_x {g x + ½‖x - z‖²}`:
`g x̄ + ½‖x̄ - z‖² ≤ g x + ½‖x - z‖²` for every `x` (in `EReal`).
Existence and uniqueness of `x̄` for proper convex lsc `g` are theorems, not part of
this predicate. -/
def IsProxPoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → EReal) (z xbar : E) : Prop :=
  ∀ x : E, g xbar + ((‖xbar - z‖ ^ 2 / 2 : ℝ) : EReal) ≤ g x + ((‖x - z‖ ^ 2 / 2 : ℝ) : EReal)

end GoldenRatioVI.Shared


