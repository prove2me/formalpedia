-- Prove2me | Definitions.Def_SuReturns_Coordination_Model
-- name    : SuReturns_Coordination_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:23.164276+00:00
-- url     : https://prove2.me/theorems/0ebcc841-2204-499d-8d50-d3bcd23af7c2
-- title:
--   Sec. 3–5, pp. 6–19 — reservation price E max(V, r), demand rule (6), and the profits (14), (15), (19), (21), (25), (31) of the supply chain contracts
-- statement:
--   This module fixes the model of Section 5 of Su, *Consumer Returns Policies and Supply Chain Performance*, which is the single-seller model of Sections 3–4 placed inside a manufacturer–retailer supply chain.
--
--   **Consumers and demand.** Market demand $X$ has law $D$ on $\mathbb R$; consumers' valuations $V$ are i.i.d. with law $\nu$ and are learned only after purchase. Under a refund $r$ a consumer who has bought keeps the product if $V \ge r$ and returns it otherwise, so
--   $$\bar G(r) = \mathbb P(V \ge r), \qquad G(r) = \mathbb P(V < r), \qquad \bar G(r) + G(r) = 1,$$
--   and the consumer's reservation price is $E\max(V, r)$. Every consumer buys at price $p$ if $p \le E\max(V,r)$ and none buys otherwise (demand rule (6)). With $E\min(X,q) = \int \min(q,x)\,dD(x)$ the expected sales of a stock $q$, the expected sales under rule (6) are
--   $$S(p,q,r) = \begin{cases} E\min(X,q), & p \le E\max(V,r),\\ 0, & \text{otherwise.}\end{cases}$$
--   The expected valuation is $\mu = EV$.
--
--   **Profits.** Let $c$ be the production cost and $s$ the salvage value. Each profit below is the paper's formula with $E\min(X,q)$ replaced by $S(p,q,r)$.
--   1. Total supply chain profit (15): $\Pi_T(p,q,r) = [(p-s)\bar G(r) + (p-r)G(r)]\,S(p,q,r) - (c-s)q$.
--   2. Retailer, standard buy-back with wholesale price $w$ and buy-back price $b$ (14): $\Pi_R(p,q,r) = [(p-b)\bar G(r) + (p-r)G(r)]\,S(p,q,r) - (w-b)q$.
--   3. Retailer, differentiated buy-back $(w,b,l)$, where unsold units are credited $b$ and returned units $b-l$ (31): $\Pi_R(p,q,r) = [(p-b)\bar G(r) + (p-r-l)G(r)]\,S(p,q,r) - (w-b)q$.
--   4. Direct-to-manufacturer returns with a buy-back $(w,b)$, where the manufacturer sets the refund $r$ and the retailer sets $p$ and $q$: retailer (19) $\Pi_R(p,q,r) = (p-b)\,S(p,q,r) - (w-b)q$; manufacturer (21) $\Pi_M(p,q,r) = [(b-s)\bar G(r) + (b-r)G(r)]\,S(p,q,r) - [(c-s)-(w-b)]q$.
--   5. Retailer, sales rebate $u$ paid on every sold unit (25): $\Pi_R(p,q,r) = [(p-s+u)\bar G(r) + (p-r+u)G(r)]\,S(p,q,r) - (w-s)q$.
--   6. Retailer, rebate $u$ paid only on units sold and kept (Sec. 5.4, p. 19): $\Pi_R(p,q,r) = [(p-s+u)\bar G(r) + (p-r)G(r)]\,S(p,q,r) - (w-s)q$.
--
--   These are the objective functions against which every coordination result of Section 5 is stated.
--
--   **Formalization Note** $\bar G$ uses the closed half-line $\{V \ge r\}$, the page's tie rule (keep at $V = r$). The valuation law is a general probability measure rather than a density $g$. Formulas (21) and (25) are the paper's compact forms of the cash flows (20) and (24); at no purchase they give $-[(c-s)-(w-b)]q$ and $-(w-s)q$, the cash flows of (20) and (24) with zero sales. The paper gives no formula for the kept-only rebate; item 6 is (24) with $u$ removed from the returned-units term, the direct reading of "the sales rebate $u$ is given only for units that are sold eventually". The single-seller model of Sections 3–4 is restated here (it is drafted separately in mission 1 of this series, and drafts cannot import drafts). $E\min(X,q)$ is `SupplyChainTheory.expSales` from the published module `SupplyChainTheory_contracts`.
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451 (version of August 2008), pp. 6–7, 10, 14, 16–19, 27: demand rule (6), (14), (15), (19), (21), (25), (31), and the kept-only rebate of Sec. 5.4

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_SuReturns_PartialRefunds_Model

open MeasureTheory

namespace SuReturns.Coordination

/-- Total supply chain profit (15), Su p. 14, with the demand rule (6). -/
noncomputable def chainProfit (ν D : Measure ℝ) (c s p q r : ℝ) : ℝ :=
  ((p - s) * SuReturns.PartialRefunds.keepProb ν r + (p - r) * SuReturns.PartialRefunds.returnProb ν r) * SuReturns.PartialRefunds.sales ν D p q r - (c - s) * q

/-- Retailer's profit under a standard buy-back contract `(w, b)`, (14), Su p. 14. -/
noncomputable def retailerBuyback (ν D : Measure ℝ) (w b p q r : ℝ) : ℝ :=
  ((p - b) * SuReturns.PartialRefunds.keepProb ν r + (p - r) * SuReturns.PartialRefunds.returnProb ν r) * SuReturns.PartialRefunds.sales ν D p q r - (w - b) * q

/-- Retailer's profit under a differentiated buy-back contract `(w, b, l)`, (31), Su p. 27:
unsold units are credited `b`, returned units `b - l`. -/
noncomputable def retailerDiffBuyback (ν D : Measure ℝ) (w b l p q r : ℝ) : ℝ :=
  ((p - b) * SuReturns.PartialRefunds.keepProb ν r + (p - r - l) * SuReturns.PartialRefunds.returnProb ν r) * SuReturns.PartialRefunds.sales ν D p q r - (w - b) * q

/-- Retailer's profit with direct-to-manufacturer returns and a buy-back `(w, b)`, (19),
Su p. 17; the refund `r` is the manufacturer's. -/
noncomputable def retailerDirect (ν D : Measure ℝ) (w b p q r : ℝ) : ℝ :=
  (p - b) * SuReturns.PartialRefunds.sales ν D p q r - (w - b) * q

/-- Manufacturer's profit with direct-to-manufacturer returns, (21), Su p. 17. -/
noncomputable def manufacturerDirect (ν D : Measure ℝ) (c s w b p q r : ℝ) : ℝ :=
  ((b - s) * SuReturns.PartialRefunds.keepProb ν r + (b - r) * SuReturns.PartialRefunds.returnProb ν r) * SuReturns.PartialRefunds.sales ν D p q r
    - ((c - s) - (w - b)) * q

/-- Retailer's profit under a SuReturns.PartialRefunds.sales rebate contract `(w, u)`, (25), Su p. 18: the rebate `u`
is paid on every unit sold, whether or not it is returned. -/
noncomputable def retailerRebate (ν D : Measure ℝ) (s w u p q r : ℝ) : ℝ :=
  ((p - s + u) * SuReturns.PartialRefunds.keepProb ν r + (p - r + u) * SuReturns.PartialRefunds.returnProb ν r) * SuReturns.PartialRefunds.sales ν D p q r - (w - s) * q

/-- Retailer's profit when the rebate `u` is paid only on units sold and kept (Su p. 19):
(24) with `u` removed from the returned-units term. -/
noncomputable def retailerKeptRebate (ν D : Measure ℝ) (s w u p q r : ℝ) : ℝ :=
  ((p - s + u) * SuReturns.PartialRefunds.keepProb ν r + (p - r) * SuReturns.PartialRefunds.returnProb ν r) * SuReturns.PartialRefunds.sales ν D p q r - (w - s) * q

end SuReturns.Coordination


