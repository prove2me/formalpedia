-- Prove2me | Definitions.Def_PELiquidity_Secondary_Market
-- name    : PELiquidity_Secondary_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T09:42:27.100614+00:00
-- url     : https://prove2.me/theorems/b6910fbb-8746-46f6-94b9-301a609643fb
-- title:
--   Definition 2: secondary-market equilibrium
-- statement:
--   A secondary-market allocation specifies the fractions of general partners raising L- and H-funds, their contracts and promised returns, the L-claim price, and quantities sold and bought. The price of an H-claim is $P_H=\delta_H\bar R_H$. The **discount to net asset value** is
--   $$D_L=1-\frac{P_L}{\bar R_L}.$$
--
--   An equilibrium requires optimal contracts, fund choice by general partners, primary capital-market clearing through the paper's supply correspondence, the secondary supply and demand schedules, and equality of secondary purchases and sales. The value of cash includes the opportunity to buy claims after a liquidity shock.
--
--   **Formalization Note** Promised returns and the L price are positive. The GP fractions are nonnegative and sum to one. A fund is raised only if its GP profit is maximal. Secondary supply is zero below the L sellers' reservation value, and secondary demand is zero above the H buyers' reservation value; the paper leaves those off-range cases implicit.
-- source:
--   Maurin, Robinson & Strömberg, A Theory of Liquidity in Private Equity, working paper (draft of December 2020), pp. 13–15, (6)–(10), Definition 2, Secondary Market; p. 26, (21)

import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting

namespace PELiquidity.Secondary

structure AllocationSec where
  αL : ℝ
  αH : ℝ
  RL : ℝ
  RH : ℝ
  PL : ℝ
  xL : ℝ
  xH : ℝ
  IL : ℝ
  IH : ℝ
  sL : ℝ
  dH : ℝ
  fL : PELiquidity.Primary.Outcome → ℝ
  fH : PELiquidity.Primary.Outcome → ℝ

noncomputable def vPE (lam δ Rb Pi : ℝ) : ℝ :=
  (1 - lam) * Rb + lam * max (δ * Rb) Pi

noncomputable def vCash (lam δ RL RH PL PH : ℝ) : ℝ :=
  (1 - lam) + lam * max 1 (δ * max (RL / PL) (RH / PH))

noncomputable def discount (E : AllocationSec) : ℝ := 1 - E.PL / E.RL

def IsEquilibriumSec (P : PELiquidity.Primary.Params) (muH : ℝ) (E : AllocationSec) : Prop :=
  0 < E.PL ∧ 0 < E.RL ∧ 0 < E.RH ∧
  PELiquidity.Primary.IsOptimalContract P E.RL (max (P.δL * E.RL) E.PL) E.xL E.IL E.fL ∧
  PELiquidity.Primary.IsOptimalContract P E.RH (P.δH * E.RH) E.xH E.IH E.fH ∧
  0 ≤ E.αL ∧ 0 ≤ E.αH ∧ E.αL + E.αH = 1 ∧
  (0 < E.αL → PELiquidity.Primary.gpProfit P E.IL E.fL ≥ PELiquidity.Primary.gpProfit P E.IH E.fH) ∧
  (0 < E.αH → PELiquidity.Primary.gpProfit P E.IH E.fH ≥ PELiquidity.Primary.gpProfit P E.IL E.fL) ∧
  PELiquidity.Primary.IsCapitalSupply (vPE P.lam P.δL E.RL E.PL)
    (vCash P.lam P.δL E.RL E.RH E.PL (P.δH * E.RH))
    ((1 - muH) * P.K) (E.αL * (E.IL - P.A)) ∧
  PELiquidity.Primary.IsCapitalSupply (vPE P.lam P.δH E.RH (P.δH * E.RH))
    (vCash P.lam P.δH E.RL E.RH E.PL (P.δH * E.RH))
    (muH * P.K) (E.αH * (E.IH - P.A)) ∧
  (E.PL = P.δL * E.RL →
    0 ≤ E.sL ∧ E.sL ≤ E.αL * (E.IL - P.A)) ∧
  (P.δL * E.RL < E.PL → E.sL = E.αL * (E.IL - P.A)) ∧
  (E.PL < P.δL * E.RL → E.sL = 0) ∧
  (E.PL < P.δH * E.RL →
    E.dH = (muH * P.K - E.αH * (E.IH - P.A)) / E.PL) ∧
  (E.PL = P.δH * E.RL →
    0 ≤ E.dH ∧ E.dH ≤ (muH * P.K - E.αH * (E.IH - P.A)) / E.PL) ∧
  (P.δH * E.RL < E.PL → E.dH = 0) ∧
  E.dH = E.sL

end PELiquidity.Secondary


