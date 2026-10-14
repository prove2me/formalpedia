-- Prove2me | Definitions.Def_ImperfectTargeting_CostlessAds_PricingGame
-- name    : ImperfectTargeting_CostlessAds_PricingGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:14.085869+00:00
-- url     : https://prove2.me/theorems/d28a9ce0-8646-4e16-8aac-7177b6cf1526
-- title:
--   §3, §4.1, pp. 8, 10 — clearinghouse price duopoly: tie-split profit with a valuation cap, mixed price strategies on [0, 1], mixed Nash equilibrium
-- statement:
--   This file defines the pricing stage of a **clearinghouse duopoly** (in the tradition of Varian and Narasimhan), the general game that every pricing subgame of the targeting model reduces to.
--
--   Two firms sell a homogeneous product at zero production cost. Firm $i \in \{1,2\}$ has a mass $L_i \ge 0$ of **loyal** consumers, who are informed only about firm $i$, and the two firms share a mass $S \ge 0$ of **shoppers**, who are informed about both. The interested consumers of firm $i$ value the product at $v_i$; in the applications, shoppers exist only when both firms serve the same consumers, so then $v_1 = v_2$.
--
--   1. **Pure-price profit.** If firm $i$ charges $p$ and its rival charges $q$, its profit is
--   $$
--   \pi(v, L, S; p, q) = \begin{cases} 0, & p > v,\\ p\,(L + S), & p \le v,\ p < q,\\ p\,(L + S/2), & p \le v,\ p = q,\\ p\,L, & p \le v,\ p > q. \end{cases}
--   $$
--   A consumer buys when the price does not exceed her valuation, shoppers buy from the cheaper firm, and on a tie they split equally.
--   2. **Mixed price strategy.** A probability measure $\mu$ on $\mathbb R$ with $\mu(\mathbb R \setminus [0,1]) = 0$.
--   3. **Expected profit.** When firm $i$ draws its price from $\mu$ and its rival, independently, from $\nu$,
--   $$
--   U(v, L, S; \mu, \nu) = \int\!\!\int \pi(v, L, S; p, q)\, \nu(dq)\, \mu(dp).
--   $$
--   4. **Mixed Nash equilibrium.** A pair $(\mu, \nu)$ of mixed price strategies such that no firm gains by deviating to any real price: for every $p' \in \mathbb R$, $\int \pi(v_1, L_1, S; p', q)\,\nu(dq) \le U(v_1, L_1, S; \mu, \nu)$, and for every $q' \in \mathbb R$, $\int \pi(v_2, L_2, S; q', p)\,\mu(dp) \le U(v_2, L_2, S; \nu, \mu)$.
--
--   Checking pure deviations suffices, since a mixed deviation is an average of pure ones.
--
--   **Formalization Note** Strategies are measures on $\mathbb R$ concentrated on $[0,1]$, the range of all valuations of the paper ($A < 1$ and $1$); on $[0,1]$ the profit is bounded and measurable, so every expected profit is a genuine Bochner integral. Deviations range over all real prices, negative ones included. The paper's "buys the product given that the price is lower than her valuation" (p. 8) is read as "not higher": the equilibrium cdf $H$ of display (2) has an atom at the valuation $1$, which earns nothing otherwise.
-- source:
--   Karle & Reisinger, Imperfect Targeting and Advertising Strategies, SSRN 4626076 (March 25, 2024), p. 8 (§3, purchase and tie rules), p. 10 (§4.1, shoppers and loyal consumers, expected profit display)

import Mathlib

open MeasureTheory

namespace ImperfectTargeting.CostlessAds

/-- Pure-price profit of a firm in a clearinghouse duopoly. The firm's interested consumers value
the product at `v`; it has a mass `L` of loyal consumers (reached only by it) and shares a mass `S`
of shoppers (reached by both firms) with its rival. With own price `p` and rival price `q`:
nobody buys above the valuation (`v < p`); otherwise the firm sells to its loyal consumers, and to
the shoppers if it is strictly cheaper, to half of them on a tie, and to none if it is dearer. -/
noncomputable def profit (v L S p q : ℝ) : ℝ :=
  if v < p then 0 else p * (L + (if p < q then S else if p = q then S / 2 else 0))

/-- A mixed price strategy: a probability measure on prices that puts no mass outside `[0, 1]`. -/
def IsStrategy (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0

/-- Expected profit of a firm (valuation `v`, loyal mass `L`, shopper mass `S`) that draws its price
from `μ` while its rival draws its price, independently, from `ν`. -/
noncomputable def expProfit (v L S : ℝ) (μ ν : Measure ℝ) : ℝ :=
  ∫ p, (∫ q, profit v L S p q ∂ν) ∂μ

/-- Nash equilibrium in mixed price strategies of the clearinghouse duopoly in which firm `i` has
valuation `vᵢ` and loyal mass `Lᵢ`, and the two firms share a shopper mass `S`. Both strategies are
mixed strategies in the sense of `IsStrategy`, and no firm gains by deviating to any real price. -/
def IsClearinghouseNE (v₁ L₁ v₂ L₂ S : ℝ) (μ ν : Measure ℝ) : Prop :=
  IsStrategy μ ∧ IsStrategy ν ∧
    (∀ p' : ℝ, ∫ q, profit v₁ L₁ S p' q ∂ν ≤ expProfit v₁ L₁ S μ ν) ∧
    (∀ q' : ℝ, ∫ p, profit v₂ L₂ S q' p ∂μ ≤ expProfit v₂ L₂ S ν μ)

end ImperfectTargeting.CostlessAds


