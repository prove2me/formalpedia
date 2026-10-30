-- Prove2me | Definitions.Def_OffPlatformThreats_Leakage_onDemand
-- name    : OffPlatformThreats_Leakage_onDemand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:31:22.129658+00:00
-- url     : https://prove2.me/theorems/48507d3a-928d-4b69-a3ae-aa80d2689f7b
-- title:
--   On-platform demand rate $\lambda_p(C, q)$
-- statement:
--   The on-platform demand rate $\lambda_p(C, q)$ of a provider who charges the fee $q$ and shares a queue with $C$ providers charging the same fee is the unique demand rate satisfying the equilibrium condition (5) on the platform.
--
--   Its closed form $\mu\, C (v - q)^+ / (c\phi + C (v - q)^+)$ is Lemma 1 of the paper, not part of the definition.
--
--   **Formalization Note** The value is defined by choice from the unique solution of (5), and is $0$ if (5) had no unique solution; Lemma 1 shows that it always has one when $c, \phi, \mu > 0$. The arguments are in the order $(C, q)$ of p. 12.
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), p. 12 (notation after (5))

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market
import Definitions.Def_OffPlatformThreats_Leakage_OnDemandEq

namespace OffPlatformThreats.Leakage

/-- **On-platform demand rate `λ^j_p(C, q)`.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), p. 12: "there are unique values of
`λ^j_{p,ℓ}, λ^j_{o,i}` that satisfy (5) … We will denote `λ^j_p(C^j_{p,ℓ}, q^j_{p,ℓ})` and
`λ^j_o(q^j_{o,i})` as these respective values."

`onDemand m C q` is the unique solution `lam` of `OnDemandEq m C q lam`.

**Formalization Note.** If (5) had no unique solution the value would be `0`; Lemma 1 (milestone
`lemma_1_unique_demand`) shows that the solution always exists and is unique when
`c, φ, µ > 0`. The demand is *not* defined by the closed form (16): that is Lemma 1. The
arguments are written in the order `(C, q)` of p. 12 (Lemma 1 writes `(q, C)`). -/
noncomputable def onDemand (m : Market) (C : ℕ) (q : ℝ) : ℝ :=
  by classical exact
    if h : ∃! lam, OnDemandEq m C q lam then h.exists.choose else 0

end OffPlatformThreats.Leakage


