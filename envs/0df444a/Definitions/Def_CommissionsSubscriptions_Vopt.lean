-- Prove2me | Definitions.Def_CommissionsSubscriptions_Vopt
-- name    : CommissionsSubscriptions_Vopt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:28:04.765898+00:00
-- url     : https://prove2.me/theorems/64ae4579-fd94-4ccc-a123-3ace036bbedf
-- title:
--   Optimal platform revenue $V_{opt}$ of problem (3)
-- statement:
--   The **optimal revenue** of the platform is
--   $$V_{opt}=\sup\Bigl\{\sum_{(i,j)\in E}(\gamma^s_i+\gamma^b_j)p_ix_{ij}+\sum_{(i,j)\in E}(\mu^s_i+\mu^b_j)x_{ij}\ :\ (p,x,q^s,q^b)\in X(\gamma,\mu),\ (\gamma,\mu)\in\Gamma\times\mathcal U\Bigr\},$$
--   the value of the platform's revenue maximization problem (3). The problem is not concave and its feasible set is not convex.
--
--   **Formalization Note** The supremum is taken in the extended reals over all feasible tuples of (3). The paper writes a maximum; that it is attained is part of Theorem 1(i).
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), (3a)–(3c), p. 10

import Mathlib
import Definitions.Def_CommissionsSubscriptions_Feasible3
import Definitions.Def_CommissionsSubscriptions_revenue

namespace CommissionsSubscriptions

/-- **The optimal revenue `V_opt` of the platform's problem (3).**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), (3a)–(3c), p. 10:
`V_opt = max_{(γ,µ,p,x,q^s,q^b)} (3a)` subject to `(p, x, q^s, q^b) ∈ X(γ, µ)`,
`(γ, µ) ∈ Γ × U`.

**Formalization Note (Reading 5).** `V_opt` is the supremum, in `EReal`, of the revenue (3a) over
all feasible tuples of (3). That the supremum is attained ("optimal solutions to (3) exist") is a
clause of Theorem 1(i), not part of the definition. -/
noncomputable def Vopt {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) : EReal :=
  ⨆ (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ)
    (_ : Feasible3 M f p x qs qb), ((revenue M f p x : ℝ) : EReal)

end CommissionsSubscriptions


