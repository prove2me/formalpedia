-- Prove2me | Definitions.Def_OffPlatformThreats_Leakage_bLeak
-- name    : OffPlatformThreats_Leakage_bLeak
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:39:10.872427+00:00
-- url     : https://prove2.me/theorems/8e15b25e-b103-422f-b156-55631d2b751a
-- title:
--   Upper end-point $b$ of the leakage interval
-- statement:
--   $$b = v + c\phi\left(1 - \left(1 + \sqrt{\tfrac{K}{c\phi\mu}}\right)^2\right).$$
--
--   For $R_o < b$ the off-platform utility $g_2(1, v - R_o) - K$ is positive; at $R_o = b$ it is zero.
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), Proposition 3, p. 18

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market

namespace OffPlatformThreats.Leakage

/-- **Upper end-point `b^j` of the leakage interval.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), Proposition 3, p. 18:
`b^j := v^j + cφ(1 − (1 + √(K^j/(cφµ)))²)`. -/
noncomputable def bLeak (m : Market) : ℝ :=
  m.v + m.c * m.phi * (1 - (1 + Real.sqrt (m.K / (m.c * m.phi * m.mu))) ^ 2)

end OffPlatformThreats.Leakage


