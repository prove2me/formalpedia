-- Prove2me | Definitions.Def_OnlineReviewPricing_priceOfDemand
-- name    : OnlineReviewPricing_priceOfDemand
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:49.754764+00:00
-- url     : https://prove2.me/theorems/4964f126-d41d-49c7-ad06-085b45630048
-- title:
--   The price–demand map $p(\lambda,n)=\mu(n)+\log((1-\lambda)/\lambda)$ (corrected: posterior mean)
-- statement:
--   The demand $\lambda=\ell(\mu(n)-p)$ is a strictly decreasing function of the price, and its inverse at state $n$ is
--
--   $$
--   p(\lambda,n)=\mu(n)+\log\frac{1-\lambda}{\lambda},\qquad \lambda\in(0,1).
--   $$
--
--   This one-to-one map between price and demand lets the fluid problem be rewritten with the demand as the control.
--
--   **Formalization Note** The e-companion writes $\mu$ where the state's posterior mean $\mu(n)$ belongs. By (1) and (2) the demand at state $n$ is $\ell(\mu(n)-p)$, and at $n=0$ this is $\ell(\mu_0-p)\ne\ell(\mu-p)$ when $\mu_0\ne\mu$. The definition uses $\mu(n)$.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), p.ec7–ec8 (PDF 44–45), the map used in (EC.14)

import Mathlib
import Definitions.Def_OnlineReviewPricing_postMean

namespace OnlineReviewPricing

/-- The price that induces demand `l` at state `n`: `p(l, n) = μ(n) + log((1 - l) / l)`
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), pp.ec7–ec8).

**Formalization Note.** The page writes `μ` where the state's posterior mean `μ(n)` belongs. By
(1)–(2) the demand is `ℓ(μ(n) - p)`, and this is its inverse in the price. For `l ∈ (0, 1)` the
logarithm's argument is positive. -/
noncomputable def priceOfDemand (μ μ₀ γ l n : ℝ) : ℝ :=
  postMean μ μ₀ γ n + Real.log ((1 - l) / l)

end OnlineReviewPricing


