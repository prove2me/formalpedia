-- Prove2me | Definitions.Def_OnlineReviewPricing_closedFormValue
-- name    : OnlineReviewPricing_closedFormValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:51.946386+00:00
-- url     : https://prove2.me/theorems/28205128-0ec2-42fe-8e2e-71bb558c39f0
-- title:
--   The closed-form revenue, right side of (16)
-- statement:
--   For a constant $z$, the **closed-form value** of (16) is
--
--   $$
--   \exp(z)\,T+\frac{\mu_0-\mu}{\gamma}\left(\log\bigl(\gamma\ell(z)T+1\bigr)-\frac{\gamma\ell(z)T}{\gamma\ell(z)T+1}\right).
--   $$
--
--   For $\gamma,T>0$ the argument of the logarithm exceeds one.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (16), p.14

import Mathlib
import Definitions.Def_OnlineReviewPricing_ell

namespace OnlineReviewPricing

/-- The right side of (16):
`exp z · T + ((μ₀ - μ) / γ) (log(γ ℓ(z) T + 1) - γ ℓ(z) T / (γ ℓ(z) T + 1))`
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (16), p.14).

**Formalization Note.** With `γ, T > 0` the logarithm's argument exceeds `1`, so `Real.log` is the
genuine logarithm. -/
noncomputable def closedFormValue (μ μ₀ γ T z : ℝ) : ℝ :=
  Real.exp z * T + (μ₀ - μ) / γ *
    (Real.log (γ * ell z * T + 1) - γ * ell z * T / (γ * ell z * T + 1))

end OnlineReviewPricing


