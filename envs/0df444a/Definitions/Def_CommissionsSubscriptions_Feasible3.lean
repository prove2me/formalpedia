-- Prove2me | Definitions.Def_CommissionsSubscriptions_Feasible3
-- name    : CommissionsSubscriptions_Feasible3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:27:06.812989+00:00
-- url     : https://prove2.me/theorems/f377517d-0d80-4d5c-baf6-0ff73846aa56
-- title:
--   Feasible set of the platform's problem (3)
-- statement:
--   A tuple $(\gamma,\mu,p,x,q^s,q^b)$ is **feasible in problem (3)** if $(\gamma,\mu)\in\Gamma\times\mathcal U$ (3c) and $(p,x,q^s,q^b)\in X(\gamma,\mu)$ is a competitive equilibrium under $(\gamma,\mu)$ (3b). The platform chooses fees, and prices form endogenously in equilibrium.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), (3b)–(3c), p. 10

import Mathlib
import Definitions.Def_CommissionsSubscriptions_InGammaU
import Definitions.Def_CommissionsSubscriptions_IsEquilibrium

namespace CommissionsSubscriptions

/-- **Feasible set of the platform's problem (3), constraints (3b)–(3c).**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), (3b)–(3c), p. 10:
`(p, x, q^s, q^b) ∈ X(γ, µ)` and `(γ, µ) ∈ Γ × U`. -/
def Feasible3 {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ) :
    Prop :=
  InGammaU f ∧ IsEquilibrium M f p x qs qb

end CommissionsSubscriptions


