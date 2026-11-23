-- Prove2me | Definitions.Def_StochSQP_Vanishing_Supplement_Deterministic
-- name    : StochSQP_Vanishing_Supplement_Deterministic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:14:36.155174+00:00
-- url     : https://prove2.me/theorems/73c97ee5-818f-4dec-acb9-4378dc136380
-- title:
--   Appendix A deterministic context and (23)
-- statement:
--   The deterministic regime uses exact gradients $g_k=\nabla f(x_k)$ and a constant $\beta_k=\beta$ satisfying
--   $$0<\beta\le1,\qquad 0<\frac{2(1-\eta)\beta\xi_{-1}\max\{\tau_{-1},1\}}{\Gamma}\le1.$$
--   These conditions supplement the published run predicate and Assumptions 1 and 3; they do not replace any algorithm update. The allowed parameters include $\theta=0$.
--
--   Feasible stationary zero-step runs are retained. As in the source's infinite-run analysis (p. 11), an infeasible-stationary finite return has already satisfied the algorithm's termination certificate. Appendix A's optional extra stationary termination test is not imposed as an additional hypothesis.
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, pp. 10, 29, (23), Appendix A

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Model

namespace StochSQP.Vanishing.Supplement

open Filter
open scoped InnerProductSpace RealInnerProductSpace Topology

variable {n m : ℕ}

/-- Condition (23), retaining β=1 and θ=0 when permitted. -/
def Cond23 (A : Params) (β : ℝ) : Prop :=
  0 < β ∧ β ≤ 1 ∧
  0 < 2 * (1 - A.η) * β * A.ξ₀ * max A.τ₀ 1 / A.Γ ∧
  2 * (1 - A.η) * β * A.ξ₀ * max A.τ₀ 1 / A.Γ ≤ 1

/-- Appendix A's deterministic context. Feasible stationary zero steps are allowed. -/
def Deterministic (P : Problem n m) (A : Params) (R : Run n m) : Prop :=
  (∀ k, R.g k = P.grad (R.x k)) ∧
  ∃ β : ℝ, Cond23 A β ∧ ∀ k, R.β k = β

end StochSQP.Vanishing.Supplement


