-- Prove2me | Definitions.Def_MarketMakerAds_Ubuy
-- name    : MarketMakerAds_Ubuy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:47.790619+00:00
-- url     : https://prove2.me/theorems/af133e74-d3b9-4ea2-9d16-01eeb6528763
-- title:
--   Utility $U_{\mathrm{buy}}(v,p_M)$ of buying the Market-Maker contract
-- statement:
--   A buyer with value $v$ who buys a unit through the Market-Maker contract at price $p_M$ pays $p_M$ with certainty. Its utility is
--
--   $$
--   U_{\mathrm{buy}}(v,p_M)=\begin{cases}v-p_M & \text{(mean-variance model)},\\ 1-e^{-\alpha (v-p_M)} & \text{(CARA model)},\end{cases}
--   $$
--
--   as in eq. (15) of the proof of Proposition 1.
--
--   Eq. (2) of the paper writes the Market-Maker utility with a positive part, $U_M(v,p_M)=(v-p_M)^+$, resp. $1-e^{-\alpha (v-p_M)^+}$; the positive part records that a buyer with $v<p_M$ does not buy. The two agree whenever $p_M\le v$.
--
--   **Formalization Note** The definition is the utility of an actual purchase; the purchase rule requires $p_M\le v$.
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, Appendix D, p.37, eq. (15); §3.3, p.12, eq. (2)

import Mathlib
import Definitions.Def_MarketMakerAds_RiskModel

namespace MarketMakerAds

/-- **Utility of buying the Market-Maker contract at price `p_M`, per unit.**
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, Appendix D,
Proof of Proposition 1, p.37, eq. (15): "If they decide to opt for the Market-Maker contract at
price pM, their utility is given by: U_M(v) = v − pM (Mean-variance model),
1 − e^{−α·v} · e^{α·pM} (CARA model)."

`Ubuy m v pM` is `v − pM` (mean-variance) and `1 − exp(−α (v − pM))` (CARA): the utility of
paying `p_M` for a unit worth `v`, with no price or allocation risk.

**Formalization Note** Eq. (2), p.12, prints the Market-Maker utility with a positive part,
`U_M(v, p_M) = (v − p_M)⁺`, resp. `1 − e^{−α(v−p_M)⁺}`; the ⁺ encodes that a buyer with
`v < p_M` does not buy. This definition is the utility of actually buying, as in (15); it equals
the printed `U_M` whenever `p_M ≤ v`, and the purchase rule `buysMM` requires `p_M ≤ v`. -/
noncomputable def Ubuy : RiskModel → ℝ → ℝ → ℝ
  | .meanVariance _, v, pM => v - pM
  | .cara α, v, pM => 1 - Real.exp (-(α * (v - pM)))

end MarketMakerAds


