-- Prove2me | Definitions.Def_OnlineReviewPricing_criticalValue
-- name    : OnlineReviewPricing_criticalValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:56.440533+00:00
-- url     : https://prove2.me/theorems/261f0fce-e79f-4ce8-9360-d5527b69597c
-- title:
--   The right side of (EC.26)
-- statement:
--   For $\kappa>0$ and a constant $z$, this is the expression
--
--   $$
--   \exp(z)+\frac{\mu_0-\mu}{\kappa}\left(\log\bigl(\kappa\ell(z)+1\bigr)-\frac{\kappa\ell(z)}{\kappa\ell(z)+1}\right).
--   $$
--
--   At a best root of the limit equation it is the limit of $\bar J^*_T/T$ as $\gamma T\to\kappa$.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (EC.26), p.ec13 (PDF 50)

import Mathlib
import Definitions.Def_OnlineReviewPricing_ell

namespace OnlineReviewPricing

/-- The right side of (EC.26):
`exp z + ((μ₀ - μ) / κ) (log(κ ℓ(z) + 1) - κ ℓ(z) / (κ ℓ(z) + 1))`
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (EC.26), p.ec13). -/
noncomputable def criticalValue (μ μ₀ κ z : ℝ) : ℝ :=
  Real.exp z + (μ₀ - μ) / κ *
    (Real.log (κ * ell z + 1) - κ * ell z / (κ * ell z + 1))

end OnlineReviewPricing


