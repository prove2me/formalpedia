-- Prove2me | Definitions.Def_CalamaiMore_Shared_IsStationaryPoint
-- name    : CalamaiMore_Shared_IsStationaryPoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:28:56.671807+00:00
-- url     : https://prove2.me/theorems/387a3fff-8429-4144-b2ff-6a25184dd07d
-- title:
--   Stationary point of $\min\{f(x) : x \in \Omega\}$, Eq. (1.5)
-- statement:
--   For the problem $\min\{f(x) : x \in \Omega\}$ (Eq. (1.1)) on a subset $\Omega$ of a finite-dimensional real inner product space, a point $x^* \in \Omega$ is a **stationary point** if it satisfies the first-order necessary condition
--
--   $$
--   \langle \nabla f(x^*), x - x^* \rangle \ge 0 \quad \text{for all } x \in \Omega.
--   $$
--
--   If the constraints defining $\Omega$ satisfy a constraint qualification, stationary points are exactly the Kuhn–Tucker points.
--
--   This definition is shared by all three missions of this series: I (convergence of the gradient projection method: Theorem 2.4, p. 100, and Lemma 3.1, p. 102), II (active-set identification: Lemma 3.1, p. 102, and the Kuhn–Tucker characterisation (4.3), p. 106) and III (finite termination for quadratic programs: Theorem 6.2, p. 111).
--
--   **Formalization Note** The predicate includes the membership $x^* \in \Omega$. $\nabla f$ is Mathlib's `gradient`.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 94, Eqs. (1.1) and (1.5)

import Mathlib

namespace CalamaiMore.Shared

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A stationary point of `min {f(x) : x ∈ Ω}`, Calamai–Moré Eq. (1.5): a point `x ∈ Ω` with
`⟨∇f(x), z - x⟩ ≥ 0` for every `z ∈ Ω`. -/
def IsStationaryPoint (f : E → ℝ) (Ω : Set E) (x : E) : Prop :=
  x ∈ Ω ∧ ∀ z ∈ Ω, 0 ≤ inner ℝ (gradient f x) (z - x)

end CalamaiMore.Shared


