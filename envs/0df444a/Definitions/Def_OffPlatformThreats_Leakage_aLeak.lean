-- Prove2me | Definitions.Def_OffPlatformThreats_Leakage_aLeak
-- name    : OffPlatformThreats_Leakage_aLeak
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:38:40.992622+00:00
-- url     : https://prove2.me/theorems/05af3241-b52a-4a97-93bd-1d161a7ef179
-- title:
--   Lower end-point $a$ of the leakage interval
-- statement:
--   $$a = v + c\phi\left(1 - \left(\Big(1 - \sqrt{\tfrac{N - 1}{N}}\Big)\sqrt{1 + \tfrac{N v}{c\phi}} + \sqrt{\tfrac{N - 1}{N}}\right)^2\right).$$
--
--   Below $a$ the platform's margin from keeping the providers on the platform is positive; above it the platform lets them go.
--
--   **Formalization Note** $N - 1$ is computed in the reals.
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), Proposition 3, p. 18

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market

namespace OffPlatformThreats.Leakage

/-- **Lower end-point `a^j` of the leakage interval.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), Proposition 3, p. 18:
`a^j := v^j + cφ(1 − ((1 − √((N^j − 1)/N^j)) √(1 + N^j v^j/(cφ)) + √((N^j − 1)/N^j))²)`.

**Formalization Note.** `N^j − 1` is computed in `ℝ` (no natural-number truncation). -/
noncomputable def aLeak (m : Market) : ℝ :=
  m.v + m.c * m.phi *
    (1 - ((1 - Real.sqrt (((m.N : ℝ) - 1) / m.N)) * Real.sqrt (1 + m.N * m.v / (m.c * m.phi))
          + Real.sqrt (((m.N : ℝ) - 1) / m.N)) ^ 2)

end OffPlatformThreats.Leakage


