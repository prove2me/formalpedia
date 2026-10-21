-- Prove2me | Definitions.Def_NatureSLT_GrowthFunction_stepFunction
-- name    : NatureSLT_GrowthFunction_stepFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:04.436893+00:00
-- url     : https://prove2.me/theorems/5dc64a8e-4bc6-4626-bef8-e4a1fee14c81
-- title:
--   Step function $\theta(z)$ of (3.22)
-- statement:
--   The **step function** $\theta : \mathbb R \to \{0, 1\}$ is
--
--   $$\theta(z) = \begin{cases} 0 & \text{if } z < 0, \\ 1 & \text{if } z \ge 0. \end{cases}$$
--
--   It turns a real-valued function into an indicator function; note the convention $\theta(0) = 1$.
--
--   **Formalization Note** The value is a boolean, `true` standing for $1$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 80, Section 3.6, below Eq. (3.22)

import Mathlib

namespace NatureSLT.GrowthFunction

/-- The **step function** of (3.22) (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed.,
§3.6, p. 80): `θ(z) = 0` if `z < 0` and `θ(z) = 1` if `z ≥ 0`. As an indicator value it is a
`Bool`, `true` standing for `1`; in particular `θ(0) = 1`. -/
noncomputable def stepFunction (z : ℝ) : Bool := decide (0 ≤ z)

end NatureSLT.GrowthFunction


