-- Prove2me | Definitions.Def_CommissionsSubscriptions_revenue
-- name    : CommissionsSubscriptions_revenue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:26:22.052578+00:00
-- url     : https://prove2.me/theorems/1a987500-dd13-4971-bfad-a81151758a80
-- title:
--   Platform revenue (3a)
-- statement:
--   The **platform's revenue** at prices $p$ and flow $x$ under fees $(\gamma,\mu)$ is
--   $$\sum_{(i,j)\in E}(\gamma^s_i+\gamma^b_j)\,p_i\,x_{ij}+\sum_{(i,j)\in E}(\mu^s_i+\mu^b_j)\,x_{ij},$$
--   the commission revenue plus the subscription revenue. It is the objective (3a) of the platform's problem (3).
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), (3a), p. 10

import Mathlib
import Definitions.Def_CommissionsSubscriptions_Market
import Definitions.Def_CommissionsSubscriptions_Fees

namespace CommissionsSubscriptions

/-- **Platform revenue, the objective (3a).**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), (3a), p. 10:
`Σ_{(i,j)∈E} (γ^s_i + γ^b_j) p_i x_{ij} + Σ_{(i,j)∈E} (µ^s_i + µ^b_j) x_{ij}`. -/
def revenue {S B : Type} (M : Market S B) (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) : ℝ :=
  ∑ e ∈ M.E, ((f.gs e.1 + f.gb e.2) * p e.1 * x e.1 e.2 + (f.ms e.1 + f.mb e.2) * x e.1 e.2)

end CommissionsSubscriptions


