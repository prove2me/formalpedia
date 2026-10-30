-- Prove2me | Definitions.Def_OffPlatformThreats_Leakage_g2
-- name    : OffPlatformThreats_Leakage_g2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:36:43.163714+00:00
-- url     : https://prove2.me/theorems/af7311cb-9fbc-46f7-b876-e63d76f3825a
-- title:
--   The revenue function $g_2(n, v)$
-- statement:
--   For $n > 0$ and $v \ge 0$,
--
--   $$g_2(n, v) = \frac{c\mu\phi}{n}\left(\sqrt{1 + n v/(c\phi)} - 1\right)^2.$$
--
--   By Lemma 2, $g_2(n, v^j)$ is the optimal on-platform revenue rate of a provider when $n$ providers are on the platform, and $g_2(1, v^j - R_o)$ the optimal off-platform revenue rate.
--
--   **Formalization Note** Lean's convention $x/0 = 0$ gives $g_2(0, v) = 0$, consistent with $U_p(\omega, 0) = -K$.
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), (18), p. 15

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market

namespace OffPlatformThreats.Leakage

/-- **The revenue function `g2`.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), (18), p. 15:
`g2(n, v) := (cµφ / n) (√(1 + n v/(cφ)) − 1)²`, for `(n, v) ∈ ℝ²₊`.

By Lemma 2, `g2(n, v^j)` is the optimal on-platform revenue rate of a provider when `n`
providers are on the platform, and `g2(1, v^j − Ro)` the optimal off-platform revenue rate.

**Formalization Note.** Lean's `x / 0 = 0` gives `g2 m 0 v = 0`, consistent with
`U_p(ω, 0) = −K` (see `Up`). On the paper's domain `v ≥ 0` the radicand is `≥ 1`. -/
noncomputable def g2 (m : Market) (n v : ℝ) : ℝ :=
  m.c * m.mu * m.phi / n * (Real.sqrt (1 + n * v / (m.c * m.phi)) - 1) ^ 2

end OffPlatformThreats.Leakage


