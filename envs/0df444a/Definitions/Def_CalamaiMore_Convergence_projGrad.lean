-- Prove2me | Definitions.Def_CalamaiMore_Convergence_projGrad
-- name    : CalamaiMore_Convergence_projGrad
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:28:41.760798+00:00
-- url     : https://prove2.me/theorems/893700d5-e6b1-4d1a-9eb8-54ede71316b4
-- title:
--   The projected gradient $\nabla_\Omega f$, Eq. (3.1)
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $\Omega \subseteq E$, $f : E \to \mathbb R$, and let $\nabla f(x)$ be the gradient of $f$ at $x$ with respect to the inner product. With $T(x)$ the tangent cone of $\Omega$ at $x$, the **projected gradient** of $f$ at $x$ is
--
--   $$
--   \nabla_\Omega f(x) = \operatorname{argmin}\{\|v + \nabla f(x)\| : v \in T(x)\},
--   $$
--
--   that is, the nearest point of $T(x)$ to $-\nabla f(x)$. When $\Omega$ is nonempty, closed and convex and $x \in \Omega$, $T(x)$ is a nonempty closed convex set, so $\nabla_\Omega f(x)$ is uniquely defined. It is a steepest descent direction for $f$ relative to $\Omega$, and it vanishes exactly at stationary points.
--
--   **Formalization Note** `projGrad f Ω x = nearestPoint (tangentCone Ω x) (-gradient f x)`, with Mathlib's `gradient` (the Riesz representative of the Fréchet derivative, $0$ where $f$ is not differentiable). The theorems of the mission use it only at points $x \in \Omega$ of a nonempty closed convex $\Omega$, where the nearest point exists and is unique.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 101, Eq. (3.1)

import Mathlib
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_CalamaiMore_Shared_tangentCone

namespace CalamaiMore.Convergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The projected gradient, Calamai–Moré Eq. (3.1):
`∇_Ω f(x) = argmin {‖v + ∇f(x)‖ : v ∈ T(x)}`, i.e. the nearest point of the tangent cone
`T(x)` to `-∇f(x)`. -/
noncomputable def projGrad (f : E → ℝ) (Ω : Set E) (x : E) : E :=
  nearestPoint (CalamaiMore.Shared.tangentCone Ω x) (-gradient f x)

end CalamaiMore.Convergence


