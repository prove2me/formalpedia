-- Prove2me | Definitions.Def_SeasonalPricing_MyopicDet_myopicRevenue
-- name    : SeasonalPricing_MyopicDet_myopicRevenue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:58:50.162476+00:00
-- url     : https://prove2.me/theorems/98fa4eec-bec7-4b89-a308-945af0780634
-- title:
--   Expected revenue of a two-price path with myopic customers and unlimited inventory, and its $c = 0$, $H = 1$ specialization
-- statement:
--   Consider the contingent pricing model with **myopic** (nonstrategic) customers: a customer arriving at time $t < T$ buys at arrival iff the current valuation is at least the premium price $p_1$; otherwise the customer waits and buys at time $T$ iff the valuation at time $T$ is at least the discount price $p_2$; customers arriving after $T$ buy iff their valuation is at least $p_2$. With unlimited inventory, the expected revenue of the price path $(p_1, p_2)$ with discount time $T$ is
--
--   $$
--   R(p_1, p_2; T) = p_1 \cdot \Lambda_I(p_1) + p_2 \cdot \big(\Lambda_W(p_1, p_2) + \Lambda_L(p_2)\big),
--   $$
--
--   where $\Lambda_I(p_1)$ is $\Lambda_I$ at the constant threshold $\psi \equiv p_1$.
--
--   The item also fixes the setting of Proposition 4: season length $H = 1$, every base valuation equal to $1$ (tail $\bar F$ of the point mass at $1$), and a decline parameter $0 < \rho < 1$ with $\alpha = -\ln \rho$, so that $\rho = e^{-\alpha H}$ is the fraction of the valuation left at the end of the season and a customer's valuation at time $t$ is $\rho^t$. The revenue in this setting is written $R_\rho(p_1, p_2; T)$; in it $\lambda$ is the expected number of arrivals over the whole season.
--
--   This is the expected revenue that the seller maximizes in Proposition 4.
--
--   **Formalization Note** The paper's $\pi^*_{C/N}$ (p. 349) uses the truncated mean $N(q, \Lambda) = \mathbb E\min\{X, q\}$, $X \sim \text{Poisson}(\Lambda)$, for finite inventory $Q$; "$Q/\lambda \to \infty$" is read as unlimited inventory, $N(q, \Lambda)$ replaced by $\Lambda$. With unlimited inventory the contingent discount chosen at $T$ does not depend on the premium-period sales, so choosing $p_2$ at $T$ as a best response and choosing $(p_1, p_2)$ jointly give the same optimum. The paper writes the myopic threshold as "$\psi(p_1) = p_1$" (p. 349), read as $\psi(t) = p_1$ for all $t$.
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 349, §6 (myopic customers, π*_{C/N}); pp. 349–350, §7 (ρ ≐ e^{−αH}, H = 1, μ = 1); p. 350, §7.1 (practically unlimited inventory); p. 351, Proposition 4

import Mathlib
import Definitions.Def_SeasonalPricing_Shared_LambdaI
import Definitions.Def_SeasonalPricing_MyopicDet_pointMassTail

namespace SeasonalPricing.MyopicDet

/-- Expected revenue of the contingent two-price policy with myopic customers (C/N) and unlimited
inventory (Aviv–Pazgal 2008, §6, p. 349, with the truncated mean `N(q, Λ)` replaced by `Λ`):
premium price `p₁` on `[0, T)`, discount price `p₂` from `T` to `H`. Myopic customers use the
constant threshold `ψ ≡ p₁`, so the premium-price sales have mean `Λ_I(p₁)`; at time `T` the
waiting customers (mean `Λ_W(p₁, p₂)`) and the late arrivals (mean `Λ_L(p₂)`) buy at `p₂`:
`p₁ · Λ_I(p₁) + p₂ · (Λ_W(p₁, p₂) + Λ_L(p₂))`. -/
noncomputable def myopicRevenue (lam α T H : ℝ) (Fbar : ℝ → ℝ) (p1 p2 : ℝ) : ℝ :=
  p1 * Shared.LambdaI lam α T Fbar (fun _ => p1) + p2 * (Shared.LambdaW lam α T Fbar p1 p2 + Shared.LambdaL lam α T H Fbar p2)

/-- The revenue `myopicRevenue` in the setting of Proposition 4 (Aviv–Pazgal 2008, p. 351):
season length `H = 1`, identical base valuations `V = 1` (`c = 0`, `μ = 1`, tail
`pointMassTail`), and decline factor `α = −ln ρ`, i.e. `ρ = e^{−αH}` is the fraction of the
valuation left at the end of the season; `T` is the discount time. -/
noncomputable def detRevenue (lam ρ : ℝ) (p1 p2 T : ℝ) : ℝ :=
  myopicRevenue lam (-Real.log ρ) T 1 pointMassTail p1 p2

end SeasonalPricing.MyopicDet


