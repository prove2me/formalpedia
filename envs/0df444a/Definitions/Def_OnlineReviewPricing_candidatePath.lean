-- Prove2me | Definitions.Def_OnlineReviewPricing_candidatePath
-- name    : OnlineReviewPricing_candidatePath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:43.733196+00:00
-- url     : https://prove2.me/theorems/17a829b2-2534-4284-8b17-0dbf85cef95f
-- title:
--   The candidate state path $n^*(t)=\ell(z)t$ of (13)
-- statement:
--   For a constant $z$, the **candidate state path** of (13) is
--
--   $$
--   n^*(t)=\ell(z)\,t ,
--   $$
--
--   the number of reviews under constant demand $\ell(z)$.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (13), p.14

import Mathlib
import Definitions.Def_OnlineReviewPricing_ell

namespace OnlineReviewPricing

/-- The state path of (13): `n*(t) = ℓ(z) t` (Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (13), p.14). -/
noncomputable def candidatePath (z t : ℝ) : ℝ :=
  ell z * t

end OnlineReviewPricing


