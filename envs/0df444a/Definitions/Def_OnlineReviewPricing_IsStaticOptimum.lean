-- Prove2me | Definitions.Def_OnlineReviewPricing_IsStaticOptimum
-- name    : OnlineReviewPricing_IsStaticOptimum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:26.512332+00:00
-- url     : https://prove2.me/theorems/7658a2cd-e5e6-4b09-8be8-242875fefa3a
-- title:
--   Static optimal prices: $\arg\max_q\,q\,\ell(m-q)$
-- statement:
--   A price $p$ is a **static optimum** at mean belief $m$ if
--
--   $$
--   p\in\arg\max_{q}\ q\,\ell(m-q).
--   $$
--
--   The two cases that matter are $p_0$ at $m=\mu_0$, the optimal price with no reviews, and $p_\infty$ at $m=\mu$, the optimal price under perfect learning.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), pp.24–25, definitions of p₀ and p_∞

import Mathlib
import Definitions.Def_OnlineReviewPricing_ell

namespace OnlineReviewPricing

/-- `p` maximizes the one-customer revenue `q ℓ(m - q)` at mean belief `m`. With `m = μ₀` this is
`p₀ := arg max_p {p ℓ(μ₀ - p)}`, and with `m = μ` it is `p_∞ := arg max_p {p ℓ(μ - p)}`
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), p.24 and p.25). -/
def IsStaticOptimum (m p : ℝ) : Prop :=
  ∀ q : ℝ, q * ell (m - q) ≤ p * ell (m - p)

end OnlineReviewPricing


