-- Prove2me | Definitions.Def_YieldPostpone_Interplay_Interaction
-- name    : YieldPostpone_Interplay_Interaction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:29.084033+00:00
-- url     : https://prove2.me/theorems/6c0c7657-717d-44bc-bc8a-7598f308efce
-- title:
--   Definition 1, p. 17 — the interaction V = (π^DR_R − π^OR_R) − (π^DA_R − π^OA_R) of the two postponements
-- statement:
--   **Definition 1** (strategic interplay of the two postponements). Fix the model's parameters and a production cost $c$. Given one strategy profile for each scenario, $\sigma^{OA},\sigma^{OR},\sigma^{DA},\sigma^{DR}$, with retailer's path profits $\pi^{OA}_R,\pi^{OR}_R,\pi^{DA}_R,\pi^{DR}_R$, the interaction is
--   $$V=\big(\pi^{DR}_R-\pi^{OR}_R\big)-\big(\pi^{DA}_R-\pi^{OA}_R\big).$$
--
--   $V$ is the gain from postponing payment when pricing is already postponed, minus that gain when pricing is not postponed. The payment postponement strategy and the pricing postponement strategy are **substitutes** if $V<0$ and **complements** if $V>0$.
--
--   The definition is meant to be evaluated at four subgame-perfect equilibria, one per scenario, each computed at the same parameters and cost; Proposition 3 states its sign on $\mathcal H_3$.
--
--   **Formalization Note** $V$ is a function of four profiles; the hypotheses that each profile is an equilibrium of its own scenario are put in the statements that use $V$.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), p. 17, Definition 1

import Mathlib
import Definitions.Def_YieldPostpone_Interplay_Setting

namespace YieldPostpone.Interplay

/-- Definition 1 (p. 17): the interaction
`V = (π^DR_R - π^OR_R) - (π^DA_R - π^OA_R)` of payment postponement and pricing postponement,
evaluated at cost `c` for four strategy profiles, one per scenario (each meant to be a
subgame-perfect equilibrium of its own scenario). The two postponements are substitutes when
`V < 0` and complements when `V > 0`. -/
def interaction (P : Params) (c : ℝ) (σOA σOR σDA σDR : Profile) : ℝ :=
  (piR P c .DR σDR - piR P c .OR σOR) - (piR P c .DA σDA - piR P c .OA σOA)

end YieldPostpone.Interplay


