-- Prove2me | Definitions.Def_OffPlatformThreats_Leakage_omegaStar
-- name    : OffPlatformThreats_Leakage_omegaStar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:38:07.118233+00:00
-- url     : https://prove2.me/theorems/8159264c-145d-4156-8b95-22cc0f1500cc
-- title:
--   Optimal payout ratio $\omega^*$ (closed form (23))
-- statement:
--   The payout ratio of Proposition 2 is
--
--   $$\omega^* = \begin{cases} \dfrac{\hat K}{g_2(N, v)}, & \text{if } \hat K \le \dfrac{c\phi\mu}{N}\left(\sqrt{1 + \dfrac{N v}{c\phi}} - 1\right)^2 - \mu R_o\left(1 - \sqrt{\dfrac{c\phi}{c\phi + N v}}\right),\\[2mm] 0, & \text{otherwise.}\end{cases}$$
--
--   This closed form is the $\omega^{j*}$ at which Proposition 3 evaluates the equilibrium. The optimality claim of Proposition 2 is not part of the definition.
--
--   **Formalization Note** At $v = 0$, $g_2(N, 0) = 0$ and Lean's $x/0 = 0$ give $\omega^* = 0$.
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), Proposition 2, (23), p. 18

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market
import Definitions.Def_OffPlatformThreats_Leakage_g2
import Definitions.Def_OffPlatformThreats_Leakage_Khat

namespace OffPlatformThreats.Leakage

/-- **The optimal payout ratio `ω^{j*}` of Proposition 2.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), Proposition 2, (23), p. 18:
`ω^{j*} = K̂^j / g2(N^j, v^j)` if
`K̂^j ≤ (cφµ/N^j)(√(1 + N^j v^j/(cφ)) − 1)² − µ Ro (1 − √(cφ/(cφ + N^j v^j)))`, and
`ω^{j*} = 0` otherwise.

**Formalization Note.** *Reading.* Proposition 3's `ω^{j*}` is this closed form (23); the
optimality claim of Proposition 2 is not part of the definition. The threshold is printed as in
(23). At `v^j = 0`, `g2(N^j, 0) = 0` and Lean's `x / 0 = 0` gives `ω^{j*} = 0` in both cases. -/
noncomputable def omegaStar (m : Market) : ℝ :=
  if Khat m ≤ m.c * m.phi * m.mu / m.N
        * (Real.sqrt (1 + m.N * m.v / (m.c * m.phi)) - 1) ^ 2
        - m.mu * m.Ro * (1 - Real.sqrt (m.c * m.phi / (m.c * m.phi + m.N * m.v)))
  then Khat m / g2 m m.N m.v
  else 0

end OffPlatformThreats.Leakage


