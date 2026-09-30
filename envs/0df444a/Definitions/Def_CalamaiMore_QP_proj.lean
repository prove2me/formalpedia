-- Prove2me | Definitions.Def_CalamaiMore_QP_proj
-- name    : CalamaiMore_QP_proj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:57:10.947978+00:00
-- url     : https://prove2.me/theorems/66854ecc-13d5-45a4-9c31-2b954d1f72ae
-- title:
--   Projection into a closed convex set, Eq. (1.3), and the projected path $x_k(\alpha)$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with norm $\|\cdot\|$, and let $\Omega \subseteq E$. The **projection** into $\Omega$ is the map $P : E \to \Omega$ given by
--
--   $$
--   P(x) = \operatorname{argmin}\{\|z - x\| : z \in \Omega\}.
--   $$
--
--   When $\Omega$ is nonempty, closed and convex, the minimiser exists and is unique, so $P(x)$ is the unique nearest point of $\Omega$ to $x$.
--
--   For a function $f : E \to \mathbb{R}$ with gradient $\nabla f$ (taken with respect to the inner product of $E$), a point $x$ and a step $\alpha$, the **projected path** is
--
--   $$
--   x(\alpha) = P\bigl(x - \alpha \nabla f(x)\bigr).
--   $$
--
--   The gradient projection step searches this path: given an iterate $x_k$ and a step $\alpha_k > 0$, the next iterate is $x_{k+1} = x_k(\alpha_k)$.
--
--   **Formalization Note** The auxiliary map `nearestPoint S x` returns some $z \in S$ with $\|z - x\| \le \|w - x\|$ for all $w \in S$ when such a point exists, and $0$ otherwise; `proj Ω = nearestPoint Ω`. The junk value is never reached when $\Omega$ is nonempty, closed and convex, and every theorem of the mission that uses $P$ assumes exactly that (for a polyhedron it follows from $x_0 \in \Omega$). $\nabla f$ is Mathlib's `gradient`, which requires $E$ to be complete (automatic in finite dimension).
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 94, Eq. (1.3); p. 97 (the path x_k(α))

import Mathlib

namespace CalamaiMore.QP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

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

/-- The projected-gradient path `x(α) = P(x - α ∇f(x))` of Calamai–Moré, p. 97. -/
noncomputable def projPath (f : E → ℝ) (Ω : Set E) (x : E) (α : ℝ) : E :=
  proj Ω (x - α • gradient f x)

end CalamaiMore.QP


