-- Prove2me | Definitions.Def_CalamaiMore_Convergence_proj
-- name    : CalamaiMore_Convergence_proj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:27:53.523378+00:00
-- url     : https://prove2.me/theorems/ff830802-83d5-467f-9523-12579c82e4fc
-- title:
--   Projection into a closed convex set, Eq. (1.3)
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with norm $\|\cdot\|$, and let $\Omega \subseteq E$. The **projection** into $\Omega$ is the map $P : E \to \Omega$ given by
--
--   $$
--   P(x) = \operatorname{argmin}\{\|z - x\| : z \in \Omega\}.
--   $$
--
--   When $\Omega$ is nonempty, closed and convex, the minimiser exists and is unique, so $P(x)$ is the unique nearest point of $\Omega$ to $x$. The projection is the basic operation of the gradient projection method, whose iterates are $x_{k+1} = P(x_k - \alpha_k \nabla f(x_k))$.
--
--   **Formalization Note** The auxiliary map `nearestPoint S x` returns some $z \in S$ with $\|z - x\| \le \|w - x\|$ for all $w \in S$ when such a point exists, and $0$ otherwise; `proj Ω = nearestPoint Ω`. The junk value is never reached when $\Omega$ is nonempty, closed and convex, and every theorem of the mission assumes exactly that.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 94, Eq. (1.3)

import Mathlib

namespace CalamaiMore.Convergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Classical in
/-- A nearest point of `S` to `x`: an element `z ∈ S` with `‖z - x‖ ≤ ‖w - x‖` for every
`w ∈ S`, chosen when one exists; the junk value `0` otherwise. For a nonempty closed convex
subset of a finite-dimensional real inner product space the nearest point exists and is unique,
so this is `argmin {‖z - x‖ : z ∈ S}`. -/
noncomputable def nearestPoint (S : Set E) (x : E) : E :=
  if h : ∃ z ∈ S, ∀ w ∈ S, ‖z - x‖ ≤ ‖w - x‖ then Classical.choose h else 0

/-- The projection into `Ω`, Calamai–Moré Eq. (1.3): `P(x) = argmin {‖z - x‖ : z ∈ Ω}`. -/
noncomputable def proj (Ω : Set E) (x : E) : E :=
  nearestPoint Ω x

end CalamaiMore.Convergence


