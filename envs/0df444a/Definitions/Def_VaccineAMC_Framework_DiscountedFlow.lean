-- Prove2me | Definitions.Def_VaccineAMC_Framework_DiscountedFlow
-- name    : VaccineAMC_Framework_DiscountedFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:58.975135+00:00
-- url     : https://prove2.me/theorems/9e042626-d506-4be0-86e6-8cb5b9a7f282
-- title:
--   Discounted value of a constant flow
-- statement:
--   For a constant real flow $f$, discount rate $r$, and measurable set of times $S$, define its present discounted value by
--
--   $$\operatorname{PDV}(r,f,S)=\int_S f e^{-rt}\,dt.$$
--
--   This general operation is used for welfare, bargaining surplus, and subsidy payments. Its value is a real Lebesgue integral; the mission applies it to exponential flows on intervals.
-- source:
--   Kremer, Levin & Snyder, Designing Advance Market Commitments for New Vaccines, BFI Working Paper No. 2020-175 (Dec. 2020), §2, p. 5 (PDF 8), discounting convention and §3.1, p. 9 (PDF 12), equation (1)

import Mathlib

namespace VaccineAMC.Framework

/-- Present discounted value of a constant real flow on a measurable time set. -/
noncomputable def discountedFlow (r f : ℝ) (S : Set ℝ) : ℝ :=
  ∫ t in S, f * Real.exp (-(r * t))

end VaccineAMC.Framework


