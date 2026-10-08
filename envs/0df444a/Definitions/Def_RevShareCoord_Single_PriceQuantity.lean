-- Prove2me | Definitions.Def_RevShareCoord_Single_PriceQuantity
-- name    : RevShareCoord_Single_PriceQuantity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T20:20:43.821999+00:00
-- url     : https://prove2.me/theorems/d0c2e823-642e-441d-9ef7-8f009b599a4c
-- title:
--   Sec. 3.1, fn. 3 — channel and retailer profits when revenue depends on both quantity q and retail price p
-- statement:
--   **Quantity and price as decisions.** Let $\mathrm{Rev}(q, p)$ be the expected revenue when $q$ units are stocked and the retail price is $p$, and let costs be linear in quantity with unit cost $c$. The integrated channel's profit and the retailer's profit under a revenue-sharing contract $\{\phi, w\}$ are
--
--   $$
--   \Pi(q, p) = \mathrm{Rev}(q, p) - cq, \qquad \pi_r(q, p, w, \phi) = \phi\,\mathrm{Rev}(q, p) - wq .
--   $$
--
--   The paper's main example is the price-dependent newsvendor, $\mathrm{Rev}(q,p) = p\bigl(q - \int_0^q F(x,p)\,dx\bigr)$ with demand distribution $F(\cdot, p)$; its footnote 3 observes that the coordination argument applies to any revenue function of price and quantity with costs linear in quantity, which is the generality of this definition.
--
--   **Formalization Note.** $\mathrm{Rev}$ is an arbitrary function $\mathbb R \times \mathbb R \to \mathbb R$ (curried); the paper writes the retailer's profit as $\phi\bigl(\mathrm{Rev}(q,p) - (w/\phi)q\bigr)$, which equals $\phi\,\mathrm{Rev}(q,p) - wq$ for $\phi \neq 0$.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 11 (PDF p. 12), Section 3.1, display of π_r(q, p, w, φ) and footnote 3

import Mathlib

namespace RevShareCoord.Single

/-- Integrated channel profit when both the quantity `q` and the retail price `p` are decision
variables (Sec. 3.1 and footnote 3, p. 11): revenue `Rev(q, p)` minus the linear cost `cq`. -/
def pqChainProfit (Rev : ℝ → ℝ → ℝ) (c q p : ℝ) : ℝ := Rev q p - c * q

/-- Retailer's profit under the revenue-sharing contract `{φ, w}` when he chooses both `q` and
`p`: `π_r(q, p, w, φ) = φ Rev(q, p) − wq` (Sec. 3.1, p. 11). -/
def pqRetailerProfit (Rev : ℝ → ℝ → ℝ) (φ w q p : ℝ) : ℝ := φ * Rev q p - w * q

end RevShareCoord.Single


