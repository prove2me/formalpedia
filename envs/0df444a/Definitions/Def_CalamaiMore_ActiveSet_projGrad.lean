-- Prove2me | Definitions.Def_CalamaiMore_ActiveSet_projGrad
-- name    : CalamaiMore_ActiveSet_projGrad
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:51:19.651296+00:00
-- url     : https://prove2.me/theorems/4ecbec5c-9dcd-487c-8ba5-135e59bf57cd
-- title:
--   The projected gradient $\nabla_\Omega f(x)$, Eq. (3.1)
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $\Omega \subseteq E$, and $f : E \to \mathbb{R}$ with gradient $\nabla f$ taken with respect to the inner product of $E$. For $x \in \Omega$ with tangent cone $T(x)$, the **projected gradient** of $f$ at $x$ is
--
--   $$
--   \nabla_\Omega f(x) = \operatorname{argmin}\{\|v + \nabla f(x)\| : v \in T(x)\},
--   $$
--
--   the point of $T(x)$ nearest to $-\nabla f(x)$. When $\Omega$ is nonempty, closed and convex, $T(x)$ is a nonempty closed convex set, so the minimiser exists and is unique. The norm $\|\nabla_\Omega f(x)\|$ measures how far $x$ is from satisfying the first-order optimality conditions of $\min\{f(x) : x \in \Omega\}$; it vanishes exactly at stationary points.
--
--   **Formalization Note** The auxiliary map `nearestPoint S y` returns some $z \in S$ with $\|z - y\| \le \|w - y\|$ for all $w \in S$ when such a point exists, and $0$ otherwise; `projGrad f Ω x = nearestPoint (tangentCone Ω x) (-∇f(x))`. The junk value is never reached for $x \in \Omega$ with $\Omega$ nonempty, closed and convex (in particular for a polyhedral $\Omega$ containing $x$). `gradient` is Mathlib's gradient, which is $0$ where $f$ is not differentiable; every theorem assumes differentiability on $\Omega$.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 101, Eq. (3.1)

import Mathlib
import Definitions.Def_CalamaiMore_Shared_tangentCone

namespace CalamaiMore.ActiveSet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open Classical in
/-- A nearest point of `S` to `y`: an element `z ∈ S` with `‖z - y‖ ≤ ‖w - y‖` for every
`w ∈ S`, chosen when one exists; the junk value `0` otherwise. For a nonempty closed convex
subset of a finite-dimensional real inner product space the nearest point exists and is unique,
so this is `argmin {‖z - y‖ : z ∈ S}`. -/
noncomputable def nearestPoint (S : Set E) (y : E) : E :=
  if h : ∃ z ∈ S, ∀ w ∈ S, ‖z - y‖ ≤ ‖w - y‖ then Classical.choose h else 0

/-- The projected gradient, Calamai–Moré Eq. (3.1):
`∇_Ω f(x) = argmin {‖v + ∇f(x)‖ : v ∈ T(x)}`, i.e. the nearest point of the tangent cone
`T(x)` to `-∇f(x)`. -/
noncomputable def projGrad (f : E → ℝ) (Ω : Set E) (x : E) : E :=
  nearestPoint (CalamaiMore.Shared.tangentCone Ω x) (-gradient f x)

end CalamaiMore.ActiveSet


