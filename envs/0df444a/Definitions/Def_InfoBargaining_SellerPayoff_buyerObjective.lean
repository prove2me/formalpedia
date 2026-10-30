-- Prove2me | Definitions.Def_InfoBargaining_SellerPayoff_buyerObjective
-- name    : InfoBargaining_SellerPayoff_buyerObjective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:14:18.331903+00:00
-- url     : https://prove2.me/theorems/84e44acd-122f-48c7-85ee-d28012ed79dc
-- title:
--   Buyer's ex ante net surplus $U_b(\alpha)$
-- statement:
--   The buyer's objective in display (6), with the linear cost $k$:
--
--   $$
--   U_b(\alpha)=\theta_b\,A(\alpha,c)-k(\alpha)=\theta_b\int_c^{\bar v}(v-c)\,dG(v,\alpha)-\bar k\,\frac{\alpha-\underline\alpha}{\bar\alpha-\underline\alpha}.
--   $$
--
--   The buyer captures the share $\theta_b$ of the realized net surplus and bears the information cost alone.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), §3.1, display (6), p. 10; linear cost p. 13

import Mathlib
import Definitions.Def_InfoBargaining_SellerPayoff_totalSurplus
import Definitions.Def_InfoBargaining_SellerPayoff_infoCost

open MeasureTheory

namespace InfoBargaining.SellerPayoff

/-- **The buyer's ex ante net surplus `U_b(α)`, display (6), with the linear cost.**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022),
§3.1, (6), p. 10: "max_α { U_b(α) = θ_b ∫_c^v̄ (v − c) dG(v, α) − k(α) }", with the linear
cost `k(α) = k̄(α − α̲)/(ᾱ − α̲)` of p. 13.

`buyerObjective μ α̲ ᾱ k̄ θ_b c α = θ_b A(α, c) − k(α)`. -/
noncomputable def buyerObjective (μ : Measure ℝ) (αl αh kbar θb c α : ℝ) : ℝ :=
  θb * totalSurplus μ α c - infoCost αl αh kbar α

end InfoBargaining.SellerPayoff


