-- Prove2me | Definitions.Def_InfoBargaining_SellerPayoff_sellerPayoffOpportunity
-- name    : InfoBargaining_SellerPayoff_sellerPayoffOpportunity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:17:11.760726+00:00
-- url     : https://prove2.me/theorems/db003c96-029c-4242-9d5f-5b9c46cdb849
-- title:
--   Seller's equilibrium payoff $V_s^*=c+\theta_sA(\alpha^*,c)$
-- statement:
--   When $c$ is the seller's **opportunity cost**, its equilibrium expected payoff is
--
--   $$
--   V_s^*=c+\theta_s\,A(\alpha^*,c),
--   $$
--
--   where $\alpha^*$ is the buyer's optimal information acquisition at bargaining power $\theta_b=1-\theta_s$.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), §3.2, unnumbered, p. 12 ("V_s∗ = c + θ_s A(α∗, c)")

import Mathlib
import Definitions.Def_InfoBargaining_SellerPayoff_optimalInfo

open MeasureTheory

namespace InfoBargaining.SellerPayoff

/-- **The seller's equilibrium expected payoff `V_s* = c + θ_s A(α*, c)` (opportunity cost).**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022),
§3.2, unnumbered, p. 12: "when c represents the seller's opportunity cost, its equilibrium
expected payoff is V_s∗ = c + θ_s A(α∗, c)".

`sellerPayoffOpportunity μ α̲ ᾱ k̄ θ_s c = c + θ_s · A(α*, c)`, with `α*` the buyer's optimal
information at bargaining power `θ_b = 1 − θ_s` (p. 7). -/
noncomputable def sellerPayoffOpportunity (μ : Measure ℝ) (αl αh kbar θs c : ℝ) : ℝ :=
  c + θs * totalSurplus μ (optimalInfo μ αl αh kbar (1 - θs) c) c

end InfoBargaining.SellerPayoff


