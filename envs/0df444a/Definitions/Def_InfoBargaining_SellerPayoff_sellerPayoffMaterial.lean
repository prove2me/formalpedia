-- Prove2me | Definitions.Def_InfoBargaining_SellerPayoff_sellerPayoffMaterial
-- name    : InfoBargaining_SellerPayoff_sellerPayoffMaterial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:16:16.237327+00:00
-- url     : https://prove2.me/theorems/d8501942-35b8-4542-a013-af1dd8b60268
-- title:
--   Seller's equilibrium payoff $U_s^*=\theta_sA(\alpha^*,c)$
-- statement:
--   When $c$ is the seller's **material cost**, its equilibrium expected payoff is
--
--   $$
--   U_s^*=\theta_s\,A(\alpha^*,c),
--   $$
--
--   where $\alpha^*$ is the buyer's optimal information acquisition at bargaining power $\theta_b=1-\theta_s$.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), §3.2, unnumbered, p. 12 ("U_s∗ = θ_s A(α∗, c)")

import Mathlib
import Definitions.Def_InfoBargaining_SellerPayoff_optimalInfo

open MeasureTheory

namespace InfoBargaining.SellerPayoff

/-- **The seller's equilibrium expected payoff `U_s* = θ_s A(α*, c)` (material cost).**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022),
§3.2, unnumbered, p. 12: "the seller's equilibrium expected payoff U_s∗ = θ_s A(α∗, c)".

`sellerPayoffMaterial μ α̲ ᾱ k̄ θ_s c = θ_s · A(α*, c)`, where `α*` is the buyer's optimal
information with bargaining power `θ_b = 1 − θ_s` ("θ_s + θ_b = 1", p. 7). -/
noncomputable def sellerPayoffMaterial (μ : Measure ℝ) (αl αh kbar θs c : ℝ) : ℝ :=
  θs * totalSurplus μ (optimalInfo μ αl αh kbar (1 - θs) c) c

end InfoBargaining.SellerPayoff


