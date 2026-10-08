-- Prove2me | Definitions.Def_SuReturns_PartialRefunds_Model
-- name    : SuReturns_PartialRefunds_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T23:07:22.018464+00:00
-- url     : https://prove2.me/theorems/5c58f60c-dd4b-4a4e-b25f-b8423201c992
-- title:
--   Sec. 3–4, pp. 6–13 — reservation price E max(V, r), demand rule (6), profits (1), (3), (7)–(8) and welfare (12)–(13)
-- statement:
--   This module fixes the single-seller model of Sections 3–4 of Su, *Consumer Returns Policies and Supply Chain Performance*.
--
--   **Consumers and demand.** Market demand $X$ has law $D$ on $\mathbb R$. Consumers' valuations $V$ are i.i.d. with law $\nu$ and are learned only after purchase. Under a refund $r$ a consumer who has bought keeps the product if $V \ge r$ and returns it otherwise, so the keep and return probabilities are
--   $$\bar G(r) = \mathbb P(V \ge r), \qquad G(r) = \mathbb P(V < r),$$
--   the consumer's reservation price is $E\max(V, r)$, and the expected valuation is $\mu = EV$. Every consumer buys at price $p$ if $p \le E\max(V, r)$ and none buys otherwise (demand rule (6)). Writing $E\min(X, q) = \int \min(q, x)\,dD(x)$ for the expected sales of a stock $q$, the expected sales under rule (6) are
--   $$S(p,q,r) = \begin{cases} E\min(X,q), & p \le E\max(V,r),\\ 0, & \text{otherwise.}\end{cases}$$
--
--   **Objectives.** Let $c$ be the unit production cost and $s$ the salvage value.
--   1. The bracket of (8), the expected margin per unit sold: $m(p,r) = (p-s)\bar G(r) + (p-r)G(r)$.
--   2. The seller's profit, cash-flow form (7): $\Pi(p,q,r) = p\bar G(r)S + (p-r+s)G(r)S + s(q - S) - cq$ with $S = S(p,q,r)$; kept units earn $p$, returned units $p - r + s$, unsold units $s$. Since $\bar G + G = 1$ this equals (8), $m(p,r)\,S - (c-s)q$.
--   3. Full refunds $r = p$, (1): $\Pi_{\text{full}}(p,q) = p\bar G(p)E\min(X,q) + sG(p)E\min(X,q) + s(q - E\min(X,q)) - cq$; every consumer buys because $E\max(V,p) \ge p$.
--   4. No returns, (3): $\Pi_{\text{no}}(q) = (\mu - s)E\min(X,q) - (c-s)q$, the newsvendor profit at price $\mu$.
--   5. Social welfare, cash-flow form (12): $SW(p,q,r) = \Big(\int_{[r,\infty)} v\,d\nu(v)\Big) S + sG(r)S + s(q - S) - cq$, which equals (13), $\int_{[r,\infty)}(v-s)\,d\nu(v)\cdot S - (c-s)q$.
--
--   These are the objective functions of Propositions 1–2 and Corollaries 1–2.
--
--   **Formalization Note** $\bar G$ uses the closed half-line $\{V \ge r\}$, the page's tie rule. The valuation law is a general probability measure rather than a density $g$, so $\int_r^\infty v g(v)\,dv$ becomes $\int_{[r,\infty)} v\,d\nu$. The demand rule (6) is built into $\Pi$ and $SW$, as the page does on pp. 10–13: formula (8) alone, maximized over all prices, is unbounded. At zero demand the profit is $sq - cq$, which is (7) with $E\min = 0$. Formula (3) fixes the price at $\mu$, as the page does. $E\min(X,q)$ is `SupplyChainTheory.expSales` from the published module `SupplyChainTheory_contracts`.
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451 (version of August 2008), pp. 6–13: (1), (3), (6), (7), (8), (12), (13)

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts

open MeasureTheory

namespace SuReturns.PartialRefunds

/-- `Ḡ(r)`: the probability that a consumer keeps the product under refund `r`,
i.e. `P(V ≥ r)` for a valuation `V ~ ν` (keep iff `V ≥ r`, Su p. 10). -/
noncomputable def keepProb (ν : Measure ℝ) (r : ℝ) : ℝ := (ν (Set.Ici r)).toReal

/-- `G(r)`: the probability that a consumer returns the product, `P(V < r)` (Su p. 10). -/
noncomputable def returnProb (ν : Measure ℝ) (r : ℝ) : ℝ := (ν (Set.Iio r)).toReal

/-- The consumer's reservation price `E max(V, r)` (Su p. 10). -/
noncomputable def reservationPrice (ν : Measure ℝ) (r : ℝ) : ℝ := ∫ v, max v r ∂ν

/-- The expected valuation `µ = E V` (Su p. 7). -/
noncomputable def meanValuation (ν : Measure ℝ) : ℝ := ∫ v, v ∂ν

/-- Expected sales `E min(X, q)`, `X ~ D`, for a stock `q` under the demand rule (6), Su p. 10:
demand is `X ~ D` if `E max(V, r) ≥ p` and `0` otherwise. -/
noncomputable def sales (ν D : Measure ℝ) (p q r : ℝ) : ℝ :=
  if p ≤ reservationPrice ν r then SupplyChainTheory.expSales D q else 0

/-- The bracket of (8), Su p. 11: the expected margin per unit sold,
`(p − s)Ḡ(r) + (p − r)G(r)`. -/
noncomputable def margin (ν : Measure ℝ) (s p r : ℝ) : ℝ :=
  (p - s) * keepProb ν r + (p - r) * returnProb ν r

/-- The seller's expected profit `Π(p, q, r)`, the cash-flow form (7), Su p. 11, with the
demand rule (6) built in: sold and kept units earn `p`, returned units `p − r + s`, unsold
units `s`, and every stocked unit costs `c`. -/
noncomputable def profit (ν D : Measure ℝ) (c s p q r : ℝ) : ℝ :=
  p * keepProb ν r * sales ν D p q r + (p - r + s) * returnProb ν r * sales ν D p q r
    + s * (q - sales ν D p q r) - c * q

/-- The seller's expected profit under a full refund `r = p`, (1), Su p. 8. Every consumer
buys, since `E max(V, p) ≥ p`. -/
noncomputable def fullRefundProfit (ν D : Measure ℝ) (c s p q : ℝ) : ℝ :=
  p * keepProb ν p * SupplyChainTheory.expSales D q
    + s * returnProb ν p * SupplyChainTheory.expSales D q
    + s * (q - SupplyChainTheory.expSales D q) - c * q

/-- The seller's expected profit when returns are not accepted, (3), Su p. 9: the price is
`µ = E V` and the seller faces a newsvendor problem. -/
noncomputable def noReturnsProfit (ν D : Measure ℝ) (c s q : ℝ) : ℝ :=
  (meanValuation ν - s) * SupplyChainTheory.expSales D q - (c - s) * q

/-- Social welfare `SW(p, q, r)`, the cash-flow form (12), Su p. 13, with the demand
rule (6) built in: kept units yield the consumer's valuation, returned and unsold units
are salvaged at `s`, and every stocked unit costs `c`. -/
noncomputable def welfare (ν D : Measure ℝ) (c s p q r : ℝ) : ℝ :=
  (∫ v in Set.Ici r, v ∂ν) * sales ν D p q r + s * returnProb ν r * sales ν D p q r
    + s * (q - sales ν D p q r) - c * q

end SuReturns.PartialRefunds


