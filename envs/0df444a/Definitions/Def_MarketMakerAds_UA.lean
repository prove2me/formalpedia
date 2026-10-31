-- Prove2me | Definitions.Def_MarketMakerAds_UA
-- name    : MarketMakerAds_UA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:32:40.056554+00:00
-- url     : https://prove2.me/theorems/4404b926-c8d8-45eb-b83f-3a6575b6d8a4
-- title:
--   Auction utility $U_A(v)$ of a buyer with value $v$
-- statement:
--   A buyer with value $v$ per unit who bids truthfully in the $(I+1)$-th price auction wins when the clearing price $p$ is below $v$ and then pays $p$. With $p$ distributed according to $h$, its **auction utility** per unit is
--
--   $$
--   U_A(v)=\begin{cases}\mathbf E_p[(v-p)^+]-\beta\,\mathrm{Var}_p[(v-p)^+] & \text{(mean-variance model)},\\[2pt] \mathbf E_p\big[1-e^{-\alpha (v-p)^+}\big] & \text{(CARA model)}.\end{cases}
--   $$
--
--   Under mean-variance, $U_A(v)$ can be negative; no outside option is built into the definition.
--
--   **Formalization Note** $(x)^+$ is `max x 0`. The law $h$ is an argument; in the market it is the law of the $(I+1)$-th highest unit value.
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, §3.3, p.12, eq. (1)

import Mathlib
import Definitions.Def_MarketMakerAds_riskUtility

open MeasureTheory

namespace MarketMakerAds

/-- **Auction utility `U_A(v)` of a buyer with value `v`, per unit.**
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, §3.3, p.12,
eq. (1): `U_A(v) = E_p[(v − p)⁺] − β · Var_p[(v − p)⁺]` (mean-variance) and
`U_A(v) = E_p[1 − e^{−α·(v−p)⁺}]` (CARA), where `p` is the auction clearing price.

`UA m h v` is `riskUtility m h (p ↦ max (v − p) 0)`: a buyer with value `v` who bids truthfully
wins exactly when the clearing price is below its value and then pays the clearing price.

**Formalization Note** `(x)⁺` is `max x 0`. The law `h` of the clearing price is an argument;
in the market (`Market.priceLaw`) it is the law of the `(I+1)`-th highest unit value. No outside
option is built in: a buyer who stays in the auction gets `U_A(v)`, also when it is negative
(mean-variance). -/
noncomputable def UA (m : RiskModel) (h : Measure ℝ) (v : ℝ) : ℝ :=
  riskUtility m h (fun p => max (v - p) 0)

end MarketMakerAds


