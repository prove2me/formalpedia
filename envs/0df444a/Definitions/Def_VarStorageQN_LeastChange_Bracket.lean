-- Prove2me | Definitions.Def_VarStorageQN_LeastChange_Bracket
-- name    : VarStorageQN_LeastChange_Bracket
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:49.962367+00:00
-- url     : https://prove2.me/theorems/118b5857-a07c-440a-8c69-3aa0eef4ca01
-- title:
--   The bracket operator [u,v] and strict positivity of an operator (§2.1)
-- statement:
--   For vectors $u,v$ in a real inner-product space $\mathcal H$, the **bracket operator** is the continuous linear map
--
--   $$[u,v]d=\langle v,d\rangle u \qquad(d\in\mathcal H).$$
--
--   The second argument is paired with the input; reversing the arguments changes the operator. A continuous linear operator $B$ on $\mathcal H$ is called **positive** if
--
--   $$\langle Bu,u\rangle>0\qquad\text{for every nonzero }u\in\mathcal H.$$
--
--   The bracket is the rank-one operator in all of the paper's secant-update formulas; positivity is the property of self-adjoint secant operators studied in Proposition A.3 and in the dfp formula (A.9).
--
--   **Formalization Note** `bracket u v` abbreviates Mathlib's `InnerProductSpace.rankOne ℝ u v`, which has the same argument order. The paper's "positive" is strict, so it is the local predicate `IsPositiveStrict`, not Mathlib's `ContinuousLinearMap.IsPositive` (which only asks $\langle Bu,u\rangle\ge0$).
-- source:
--   Gilbert & Lemaréchal, Some numerical experiments with variable-storage quasi-Newton algorithms, IIASA Working Paper WP-88-121 (August 1988), p. 3, §2.1

import Mathlib

namespace VarStorageQN.LeastChange

open InnerProductSpace
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The bracket operator `[u,v] d = ⟪v,d⟫ u` (§2.1, p. 3). -/
noncomputable abbrev bracket (u v : H) : H →L[ℝ] H := rankOne ℝ u v

/-- "B is positive" in the paper's strict sense (§2.1, p. 3):
`⟪B u, u⟫ > 0` for every nonzero `u`. -/
def IsPositiveStrict (B : H →L[ℝ] H) : Prop := ∀ u : H, u ≠ 0 → 0 < ⟪B u, u⟫_ℝ

end VarStorageQN.LeastChange


