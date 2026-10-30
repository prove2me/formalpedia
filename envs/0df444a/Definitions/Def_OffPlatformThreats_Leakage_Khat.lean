-- Prove2me | Definitions.Def_OffPlatformThreats_Leakage_Khat
-- name    : OffPlatformThreats_Leakage_Khat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:37:33.45521+00:00
-- url     : https://prove2.me/theorems/9d407207-f9b2-4015-a772-087a10959cfb
-- title:
--   Non-platform opportunity cost $\hat K$
-- statement:
--   Combining the off-platform and outside options into one non-platform option, a provider's opportunity cost of joining the platform is
--
--   $$\hat K = \max\{K,\ g_2(1, (v - R_o)^+)\}.$$
--
--   **Formalization Note** The paper writes $g_2(1, v - R_o)$ in (21); the positive part keeps $g_2$ on its domain $\mathbb{R}^2_+$ and agrees with (21) whenever $v \ge R_o$. For $v < R_o$ it is the off-platform revenue $0$.
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), (21), p. 16

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market
import Definitions.Def_OffPlatformThreats_Leakage_g2

namespace OffPlatformThreats.Leakage

/-- **The non-platform opportunity cost `K̂^j`.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), (21), p. 16:
`K̂^j := max{K^j, g2(1, v^j − Ro)}`.

**Formalization Note.** *Generalization.* The second argument is `(v^j − Ro)^+`, so that `g2`
is never evaluated outside its domain `ℝ²₊` (p. 15). It agrees with (21) whenever
`v^j ≥ Ro`, and for `v^j < Ro` it is the off-platform revenue `0` of Lemma 2 (every fee then
attracts no off-platform demand). -/
noncomputable def Khat (m : Market) : ℝ :=
  max m.K (g2 m 1 (max (m.v - m.Ro) 0))

end OffPlatformThreats.Leakage


