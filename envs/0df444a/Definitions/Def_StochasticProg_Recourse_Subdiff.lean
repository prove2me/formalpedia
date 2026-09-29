-- Prove2me | Definitions.Def_StochasticProg_Recourse_Subdiff
-- name    : StochasticProg_Recourse_Subdiff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T04:46:05.361605+00:00
-- url     : https://prove2.me/theorems/241a6099-53ea-4322-b978-e216a3513fb2
-- title:
--   Subdifferential of the recourse function
-- statement:
--   For a two-stage recourse instance and a point $x$, the **subdifferential** $\partial Q(x)$ is the
--   set of $\eta \in \mathbb{R}^{n_1}$ satisfying the subgradient inequality
--   $$Q(x) + \eta^{\mathsf T}(y - x) \le Q(y) \qquad \text{for all } y \in \mathbb{R}^{n_1},$$
--   where $Q$ is the extended-real-valued recourse function of `StochasticProg.Recourse.Q` (Birge &
--   Louveaux, p. 115, the object appearing in Theorem 9's optimality condition (1.12)).
--
--   **Formalization Note.** Adding the finite real $\eta^{\mathsf T}(y-x)$ to the possibly-infinite
--   $Q(x)$ uses `EReal`'s native addition, which is unambiguous whenever at most one summand is
--   infinite -- the only case that occurs here.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 115, Chapter 3, Section 3.1e

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance

namespace StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- The subdifferential `∂Q(x)` of the (extended-real-valued) recourse function,
via the subgradient inequality `Q(x) + ηᵀ(y-x) ≤ Q(y)` for all `y` (p. 115). Adding
the finite real `ηᵀ(y-x)` to `Q(x)` uses `EReal`'s own addition, which agrees with
the book's convention whenever at most one of the two summands is infinite. -/
noncomputable def subdiffQ (inst : Instance n1 n2 m1 m2 K) (x : Fin n1 → ℝ) :
    Set (Fin n1 → ℝ) :=
  {η | ∀ y : Fin n1 → ℝ,
    Q inst x + ((dotProduct η (y - x) : ℝ) : EReal) ≤ Q inst y}

end StochasticProg.Recourse


