-- Prove2me | Definitions.Def_MarketMakerAds_pStar
-- name    : MarketMakerAds_pStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:40.314012+00:00
-- url     : https://prove2.me/theorems/73afee9a-d885-4644-b635-1b7c70436dcf
-- title:
--   The Market-Maker price $p^*_M$, closed form (3)
-- statement:
--   For a law $h$ of the auction clearing price $p$, with mean $\mu_A$ and variance $\sigma_A^2$, the **Market-Maker price** is
--
--   $$
--   p^*_M=\begin{cases}\mu_A+\beta\,\sigma_A^2 & \text{(mean-variance model)},\\[2pt] \dfrac1\alpha\log\mathbf E_p\big[e^{\alpha p}\big] & \text{(CARA model)}.\end{cases}
--   $$
--
--   It is the price at which buyers with value at least the top $p_{\max}$ of the support of $h$ are indifferent between the contract and the auction (Proposition 1).
--
--   **Formalization Note** The restatement on p.37 omits the logarithm; eq. (3) on p.17 has it, and that is the definition. At $\alpha=0$ the CARA formula is undefined (Lean returns $0$); theorems about $p^*_M$ assume $\alpha>0$.
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, Proposition 1, p.17, eq. (3)

import Mathlib
import Definitions.Def_MarketMakerAds_RiskModel

open MeasureTheory

namespace MarketMakerAds

/-- **The Market-Maker price `p*_M`, closed form (3).**
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, Proposition 1,
p.17, eq. (3): "p*_M = µ_A + β · σ²_A (Mean-variance model), (1/α) · log(E_p[e^{α·p}]) (CARA
model)", where µ_A and σ_A are the mean and standard deviation of the auction clearing price.

`pStar m h` is `∫ p dh + β · ∫ (p − ∫ q dh)² dh` (mean-variance) and
`(1/α) · log ∫ e^{α p} dh(p)` (CARA), for the law `h` of the clearing price.

**Formalization Note** The restatement inside the proof on p.37 omits the `log`; eq. (3) on p.17
has it, and that is the definition used. The value at `α = 0` is Lean's junk `0` (`1/0 = 0`);
every theorem about `pStar` assumes `α > 0` (`RiskModel.IsAdmissible`). -/
noncomputable def pStar : RiskModel → Measure ℝ → ℝ
  | .meanVariance β, h => (∫ p, p ∂h) + β * ∫ p, (p - ∫ q, q ∂h) ^ 2 ∂h
  | .cara α, h => (1 / α) * Real.log (∫ p, Real.exp (α * p) ∂h)

end MarketMakerAds


