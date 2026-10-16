-- Prove2me | Definitions.Def_PELiquidity_Primary_Market
-- name    : PELiquidity_Primary_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:56.653541+00:00
-- url     : https://prove2.me/theorems/ffc59c79-151c-4a3f-8a4a-1c5c9b4f8962
-- title:
--   Definition 2 (No Secondary Market), p. 15 — private equity market equilibrium with L- and H-funds
-- statement:
--   The private equity market equilibrium of Definition 2 when there is no secondary market for partnership claims.
--
--   An **allocation** consists of the fractions $\alpha_L,\alpha_H$ of GPs raising an $L$-fund and an $H$-fund, the expected returns $\bar R_{PE,L},\bar R_{PE,H}$ promised to the LPs of each fund type, and contracts $(x_L,I_L,f_L)$, $(x_H,I_H,f_H)$. Without a secondary market the value of cash is $v_{cash,i}=1$ and the claim price is $P_i=\delta_i\bar R_{PE,i}$, so the value (6) of a unit of private equity to an $i$-LP is
--   $$v_{PE,i}=(1-\lambda)\bar R_{PE,i}+\lambda\,\delta_i\bar R_{PE,i}.$$
--
--   Given the capital share $\mu_H$ of $H$-LPs ($\mu_L=1-\mu_H$), the allocation is an **equilibrium** if
--
--   1. (Optimal Partnership) for $i=L,H$ the contract $(x_i,I_i,f_i)$ solves (5) at the return $\bar R_{PE,i}$, with the no-default constraint $1-x_i\le\delta_i\bar R_{PE,i}$;
--   2. (GP Fund Choice) $\alpha_L,\alpha_H\ge 0$, $\alpha_L+\alpha_H=1$, and a fund type is raised only if it is profit-maximizing: $\alpha_L>0$ implies $\Pi_{GP,H}\le\Pi_{GP,L}$, and $\alpha_H>0$ implies $\Pi_{GP,L}\le\Pi_{GP,H}$, where $\Pi_{GP,i}=\bar f_i I_i$;
--   3. (Primary Market clearing) the capital raised, $S_i=\alpha_i(I_i-A)$, is an admissible supply (7) of $i$-LPs at $v_{PE,i}$ versus $v_{cash,i}=1$ with capacity $\mu_i K$.
--
--   This is the equilibrium notion whose comparative statics in $\mu_H$ are the subject of Proposition 2.
--
--   **Formalization Note** Three readings of Definition 2 are fixed here. The fractions sum to one (every GP raises one fund; the paper's proof uses this in (C.4)). GP Fund Choice is the "only if" direction of the printed "$\alpha_i^*>0$ if and only if $\Pi^*_{GP,i}=\max\{\Pi^*_{GP,L},\Pi^*_{GP,H}\}$": the literal biconditional forces both fund types to be raised at every profit tie, which leaves no equilibrium at the threshold $\underline\mu_H$ of Proposition 2. The capital share $\mu_H$ is a parameter of the predicate, not of the allocation.
-- source:
--   Maurin, Robinson & Strömberg, A Theory of Liquidity in Private Equity, working paper (draft of December 2020), pp. 13–15, (6), (7), Definition 2 (item 4, No Secondary Market)

import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting

namespace PELiquidity.Primary

/-- An allocation of Definition 2 without a secondary market: fund composition `αL, αH`,
expected returns `RL, RH` (`R̄_PE,L`, `R̄_PE,H`), and the partnership contracts
`(xL, IL, fL)`, `(xH, IH, fH)`. Secondary prices are not a field: by item 4 they equal
`δ_i R̄_PE,i`. -/
structure Allocation where
  αL : ℝ
  αH : ℝ
  RL : ℝ
  RH : ℝ
  xL : ℝ
  xH : ℝ
  IL : ℝ
  IH : ℝ
  fL : Outcome → ℝ
  fH : Outcome → ℝ

/-- Private equity market equilibrium (Definition 2) with no secondary market
(`v_cash,i = 1`, `P_i = δ_i R̄_PE,i`), for the capital share `muH` of H-LPs. -/
def IsEquilibrium (P : Params) (muH : ℝ) (E : Allocation) : Prop :=
  IsOptimalContract P E.RL (P.δL * E.RL) E.xL E.IL E.fL ∧
  IsOptimalContract P E.RH (P.δH * E.RH) E.xH E.IH E.fH ∧
  0 ≤ E.αL ∧ 0 ≤ E.αH ∧ E.αL + E.αH = 1 ∧
  (0 < E.αL → gpProfit P E.IH E.fH ≤ gpProfit P E.IL E.fL) ∧
  (0 < E.αH → gpProfit P E.IL E.fL ≤ gpProfit P E.IH E.fH) ∧
  IsCapitalSupply ((1 - P.lam) * E.RL + P.lam * (P.δL * E.RL)) 1
    ((1 - muH) * P.K) (E.αL * (E.IL - P.A)) ∧
  IsCapitalSupply ((1 - P.lam) * E.RH + P.lam * (P.δH * E.RH)) 1
    (muH * P.K) (E.αH * (E.IH - P.A))

end PELiquidity.Primary


