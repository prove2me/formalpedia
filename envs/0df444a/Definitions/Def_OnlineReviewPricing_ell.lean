-- Prove2me | Definitions.Def_OnlineReviewPricing_ell
-- name    : OnlineReviewPricing_ell
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:37.604833+00:00
-- url     : https://prove2.me/theorems/ece54ba3-985d-405d-8a6a-aa43794aabfa
-- title:
--   The logit function $\ell(\chi)=\exp(\chi)/(1+\exp(\chi))$
-- statement:
--   The **logit function** is
--
--   $$
--   \ell(\chi)=\frac{\exp(\chi)}{1+\exp(\chi)},\qquad \chi\in\mathbb R .
--   $$
--
--   A customer whose expected utility of a purchase is $\chi$ buys with probability $\ell(\chi)$. This is the purchase probability under Gumbel utility noise, and it is the only nonlinearity of the fluid model.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (1), p.7

import Mathlib

namespace OnlineReviewPricing

/-- The logit `ℓ(χ) = exp χ / (1 + exp χ)`, the demand function (1)
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (1), p.7). -/
noncomputable def ell (z : ℝ) : ℝ :=
  Real.exp z / (1 + Real.exp z)

end OnlineReviewPricing


