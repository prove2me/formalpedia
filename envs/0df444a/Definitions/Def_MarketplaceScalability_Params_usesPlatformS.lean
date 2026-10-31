-- Prove2me | Definitions.Def_MarketplaceScalability_Params_usesPlatformS
-- name    : MarketplaceScalability_Params_usesPlatformS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:50:07.383635+00:00
-- url     : https://prove2.me/theorems/6e353196-5863-443d-87fd-b584da554f7c
-- title:
--   Sellers use the platform service in the scalable scenario
-- statement:
--   In the scalable scenario, sellers use the platform service at price $p$ when $p\le\bar c$ and
--   $$
--   (1-\alpha)R(q_o)-\underline c\,q_o-F\;\le\;(1-\alpha)R(q(p))-p\,q(p)-f.
--   $$
--   The right side is the payoff at the platform service, and the left side is the payoff from investing and using own service. A seller who is indifferent uses the platform service, as in (6).
--
--   **Formalization Note** The cutoff $p_s$ does not appear here: it is constructed from this comparison, in a theorem of the mission. The test $p\le\bar c$ comes first because $q(p)$ is meaningful only for such $p$. Above $\bar c$ the platform service is strictly worse than the market at every output, and the market is worse than own service by Assumption 1.
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, §3.1, p.9

import Mathlib
import Definitions.Def_MarketplaceScalability_Params_sellerPayoff

namespace MarketplaceScalability

/-- In the scalable scenario, sellers use the platform service at price `p`: the price is at most the
market cost `c̄`, and the payoff at the platform service `(p, f)` is at least the payoff
`(1 − α) R(q_o) − c̲ q_o − F` of own service. Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484, §3.1, p.9.

**Formalization Note** The cutoff `p_s` does not appear here: it is constructed from this comparison in
`cutoff_price`. A seller indifferent between the two uses the platform service, as in (6). The test
`p ≤ c̄` comes first because `q p` is meaningful only for such `p`; above `c̄` the platform service is
strictly worse than the market at every output (`seller_service_choice`), and the market is worse
than own service (Assumption 1). -/
def Params.usesPlatformS (P : Params) (p : ℝ) : Prop :=
  p ≤ P.cbar ∧ P.sellerPayoff P.cown P.F ≤ P.sellerPayoff p P.f

end MarketplaceScalability


