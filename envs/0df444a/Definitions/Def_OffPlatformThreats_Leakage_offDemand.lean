-- Prove2me | Definitions.Def_OffPlatformThreats_Leakage_offDemand
-- name    : OffPlatformThreats_Leakage_offDemand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:32:04.088654+00:00
-- url     : https://prove2.me/theorems/4822d6dc-f43d-4713-b747-7d1dc8e231b5
-- title:
--   Off-platform demand rate $\lambda_o(q)$
-- statement:
--   The off-platform demand rate $\lambda_o(q)$ of a provider who charges the fee $q$ off the platform is the unique demand rate satisfying the off-platform equilibrium condition (5).
--
--   Its closed form $\mu (v - q - R_o)^+ / (c\phi + (v - q - R_o)^+)$ is Lemma 1 of the paper, not part of the definition.
--
--   **Formalization Note** Defined by choice from the unique solution of (5), and $0$ if there were none; Lemma 1 shows there always is one when $c, \phi, \mu > 0$.
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), p. 12 (notation after (5))

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market
import Definitions.Def_OffPlatformThreats_Leakage_OffDemandEq

namespace OffPlatformThreats.Leakage

/-- **Off-platform demand rate `λ^j_o(q)`.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), p. 12: the unique value
`λ^j_o(q^j_{o,i})` satisfying (5).

`offDemand m q` is the unique solution `lam` of `OffDemandEq m q lam`.

**Formalization Note.** If (5) had no unique solution the value would be `0`; Lemma 1 shows it
always has one when `c, φ, µ > 0`. Not defined by the closed form (17), which is Lemma 1. -/
noncomputable def offDemand (m : Market) (q : ℝ) : ℝ :=
  by classical exact
    if h : ∃! lam, OffDemandEq m q lam then h.exists.choose else 0

end OffPlatformThreats.Leakage


