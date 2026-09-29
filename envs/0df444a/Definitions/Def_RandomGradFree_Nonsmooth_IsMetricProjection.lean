-- Prove2me | Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
-- name    : RandomGradFree_Nonsmooth_IsMetricProjection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T07:07:20.556991+00:00
-- url     : https://prove2.me/theorems/76ba5b2c-2d63-48c7-96ac-f8476e31f156
-- title:
--   Euclidean projection $z = \pi_Q(y)$ as a predicate
-- statement:
--   Let $Q \subseteq E$ and $y, z \in E$. We say that $z$ is a **Euclidean projection of $y$ onto $Q$** if
--
--   $$
--   z \in Q \quad\text{and}\quad \|y - z\| \le \|y - w\| \ \text{ for all } w \in Q .
--   $$
--
--   When $Q$ is nonempty, closed and convex in a finite-dimensional inner product space, such a point exists and is unique; it is the projection $\pi_Q(y)$ used by the random search method.
--
--   **Formalization Note** Mathlib has no projection function onto a closed convex set, so the projection is expressed as this relation; for the sets used in the mission it determines $\pi_Q(y)$ uniquely.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 541, Section 4, notation π_Q after Eq. (39)

import Mathlib

namespace RandomGradFree.Nonsmooth

/-- `z` is a Euclidean projection of `y` onto `Q`: `z ∈ Q` and `z` is a nearest point of `Q`
to `y`. For a nonempty closed convex `Q` in a finite-dimensional inner product space such a
`z` exists and is unique; it is the paper's `π_Q(y)` (p. 541). -/
def IsMetricProjection {E : Type*} [NormedAddCommGroup E] (Q : Set E) (y z : E) : Prop :=
  z ∈ Q ∧ ∀ w ∈ Q, ‖y - z‖ ≤ ‖y - w‖

end RandomGradFree.Nonsmooth


