-- Prove2me | Definitions.Def_OnlineReviewPricing_demand
-- name    : OnlineReviewPricing_demand
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:32.201184+00:00
-- url     : https://prove2.me/theorems/bd9159c3-cee7-47a9-9a54-9aac594c8be2
-- title:
--   Fluid demand $\lambda=\ell(\mu(n)-p)$ at price $p$ and state $n$
-- statement:
--   With the paper's normalization of the valuation, a customer's expected utility of buying at price $p$ after $n$ reviews is $\mu(n)-p$. The fluid **demand** is therefore
--
--   $$
--   \lambda(p,n)=\ell\bigl(\mu(n)-p\bigr).
--   $$
--
--   In the fluid model the average rating is the constant $\mu$, so the state of the review platform reduces to the number of reviews $n$. Every purchase produces a review ($u=1$, footnote 3, p.7), so $\lambda$ is also the rate at which reviews arrive.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (1), p.7, with (2), p.7 and q̄(t) = µ, p.12

import Mathlib
import Definitions.Def_OnlineReviewPricing_ell
import Definitions.Def_OnlineReviewPricing_postMean

namespace OnlineReviewPricing

/-- The demand at price `p` when `n` reviews have been posted: `λ(p, n) = ℓ(μ(n) - p)`
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (1) and (2), p.7, with `q̄(t) = μ`, p.12).

**Formalization Note.** The normalization `(α, β) = (1, 0)` of p.6 is built in: the expected
utility is the posterior mean minus the price. The state `Φ = (n, q̄)` reduces to `n`, because
`q̄ = μ` is constant in the fluid model. -/
noncomputable def demand (μ μ₀ γ p n : ℝ) : ℝ :=
  ell (postMean μ μ₀ γ n - p)

end OnlineReviewPricing


