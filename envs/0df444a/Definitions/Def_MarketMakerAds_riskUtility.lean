-- Prove2me | Definitions.Def_MarketMakerAds_riskUtility
-- name    : MarketMakerAds_riskUtility
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:37.171557+00:00
-- url     : https://prove2.me/theorems/29f58fa2-c468-443a-bfee-0e5465b7d5f3
-- title:
--   Risk-averse utility of a random payoff $X(p)$
-- statement:
--   Let the auction clearing price $p$ have law $\mu$ on $\mathbb R$ and let $X(p)$ be a payoff that depends on it. Its **utility** is
--
--   $$
--   U(X)=\begin{cases}\mathbf E_\mu[X]-\beta\,\mathbf E_\mu\big[(X-\mathbf E_\mu X)^2\big] & \text{(mean-variance model)},\\[2pt] \mathbf E_\mu\big[1-e^{-\alpha X}\big] & \text{(CARA model)}.\end{cases}
--   $$
--
--   Applied to the auction payoff $X(p)=(v-p)^+$ this is the auction utility of eq. (1); applied to the payoff of a misreport it is the utility $U_{\mathrm{lie}}$ of Theorem 1.
--
--   **Formalization Note** The variance is written as the integral of the squared deviation from the mean. Lean's integral of a non-integrable function is $0$; every theorem using this definition assumes the moments that make the integrals finite.
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, §3.3, p.12, eq. (1); Appendix B, p.30

import Mathlib
import Definitions.Def_MarketMakerAds_RiskModel

open MeasureTheory

namespace MarketMakerAds

/-- **Risk-averse utility of a random payoff.**
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, §3.3, p.12,
eq. (1): the mean-variance utility `E_p[X] − β · Var_p[X]` and the CARA utility
`E_p[1 − e^{−α·X}]` of a payoff `X(p)` that depends on the auction clearing price `p`.

`riskUtility m μ X` is the utility of the payoff `X : ℝ → ℝ` when the clearing price `p` has
law `μ`:
* mean-variance `β`: `∫ X dμ − β · ∫ (X − ∫ X dμ)² dμ`;
* CARA `α`: `∫ (1 − exp(−α · X)) dμ`.

**Formalization Note** The variance is written as the integral of the squared deviation from the
mean. Lean's Bochner integral is `0` for a non-integrable integrand; every theorem that uses
this definition carries the moment hypothesis that makes the integrals finite. The same function
is applied to the truthful payoff `(v − p)⁺` (eq. (1)) and to a misreport payoff (Theorem 1). -/
noncomputable def riskUtility : RiskModel → Measure ℝ → (ℝ → ℝ) → ℝ
  | .meanVariance β, μ, X => (∫ p, X p ∂μ) - β * ∫ p, (X p - ∫ q, X q ∂μ) ^ 2 ∂μ
  | .cara α, μ, X => ∫ p, (1 - Real.exp (-(α * X p))) ∂μ

end MarketMakerAds


