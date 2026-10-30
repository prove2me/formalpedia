-- Prove2me | Definitions.Def_CommissionsSubscriptions_IsOptimalPair
-- name    : CommissionsSubscriptions_IsOptimalPair
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:29:01.709468+00:00
-- url     : https://prove2.me/theorems/8b9f9c71-a7b7-4a7a-b524-7bab5fbaa940
-- title:
--   Optimal commission-subscription pair, $V(\gamma,\mu)=V_{opt}$
-- statement:
--   A pair $(\gamma,\mu)$ is an **optimal commission-subscription pair** if $(\gamma,\mu)\in\Gamma\times\mathcal U$ and the platform's revenue $V(\gamma,\mu)$ under it equals $V_{opt}$.
--
--   **Formalization Note** $V(\gamma,\mu)=V_{opt}$ is stated as: some competitive equilibrium under $(\gamma,\mu)$ has revenue $V_{opt}$. Equilibria exist (Proposition 1) and all equilibria under $(\gamma,\mu)$ give the same revenue (Corollary 1), so this is the paper's notion; both facts are milestones of the mission.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), p. 11 (definition of V(γ, µ) and of an optimal commission-subscription vector)

import Mathlib
import Definitions.Def_CommissionsSubscriptions_Vopt

namespace CommissionsSubscriptions

/-- **An optimal commission-subscription pair, `V(γ, µ) = V_opt`.**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), p. 11: "we denote by `V(γ, µ)` the platform's revenues
achieved under commission-subscription pair `(γ, µ)`. We refer to `(γ, µ)` such that
`V(γ, µ) = V_opt` as an optimal commission-subscription vector."

**Formalization Note (Reading 4).** `(γ, µ) ∈ Γ × U` and some competitive equilibrium under
`(γ, µ)` has revenue `V_opt`. By Proposition 1 an equilibrium exists and by Corollary 1 all
equilibria under `(γ, µ)` have the same revenue, so this is the paper's `V(γ, µ) = V_opt`; both
facts are milestones of the mission. -/
def IsOptimalPair {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (f : Fees S B) : Prop :=
  InGammaU f ∧ ∃ (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ),
    IsEquilibrium M f p x qs qb ∧ ((revenue M f p x : ℝ) : EReal) = Vopt M

end CommissionsSubscriptions


