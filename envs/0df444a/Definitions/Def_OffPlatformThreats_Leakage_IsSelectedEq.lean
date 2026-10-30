-- Prove2me | Definitions.Def_OffPlatformThreats_Leakage_IsSelectedEq
-- name    : OffPlatformThreats_Leakage_IsSelectedEq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:35:36.064615+00:00
-- url     : https://prove2.me/theorems/ec640a98-4db1-4527-9ae5-e7fa82ba978a
-- title:
--   The selected participation equilibrium
-- statement:
--   When several participation equilibria exist, the paper assumes, following Taylor (2018), that providers settle on the one with the higher number of providers. A pair $(N_p, N_o)$ is the **selected equilibrium** at payout ratio $\omega$ if it is a participation equilibrium (Definition 1, corrected) and no participation equilibrium at $\omega$ has more providers on the platform.
--
--   **Formalization Note** "Higher provider numbers" is read as the largest number $N_p$ of providers on the platform, which is how the paper applies the rule to Proposition 1.
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), p. 16 (selection rule after Proposition 1)

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market
import Definitions.Def_OffPlatformThreats_Leakage_IsParticipationEq

namespace OffPlatformThreats.Leakage

/-- **The selected participation equilibrium.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), p. 16 (unnumbered): "We follow the
example of Taylor (2018) and will assume that for the parameter combinations resulting in
multiple equilibria, providers “settle” on the equilibrium that corresponds to higher provider
numbers."

`IsSelectedEq m ω np no` says that `(np, no)` is a participation equilibrium (corrected
Definition 1) with the largest number `np` of providers on the platform among all participation
equilibria at `ω`.

**Formalization Note.** *Reading.* "Higher provider numbers" is read as the largest number of
providers *on the platform*, which is what Proposition 1 (22) and the proof of Proposition 2
(Appendix p. 4) resolve with it; `N^j_o` is not maximized. -/
def IsSelectedEq (m : Market) (ω : ℝ) (np no : ℕ) : Prop :=
  IsParticipationEq m ω np no ∧ ∀ np' no' : ℕ, IsParticipationEq m ω np' no' → np' ≤ np

end OffPlatformThreats.Leakage


