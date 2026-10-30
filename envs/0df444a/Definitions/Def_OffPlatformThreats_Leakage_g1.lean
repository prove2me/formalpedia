-- Prove2me | Definitions.Def_OffPlatformThreats_Leakage_g1
-- name    : OffPlatformThreats_Leakage_g1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:36:07.255031+00:00
-- url     : https://prove2.me/theorems/378a54bb-8856-4336-aa29-0ad4eae584d6
-- title:
--   The fee function $g_1(n, v)$
-- statement:
--   For $n > 0$ and $v \ge 0$,
--
--   $$g_1(n, v) = \frac{n v + c\phi - c\phi\sqrt{1 + n v/(c\phi)}}{n}.$$
--
--   By Lemma 2, $g_1(n, v^j)$ is the optimal on-platform fee when $n$ providers are on the platform, and $g_1(1, v^j - R_o)$ the optimal off-platform fee.
--
--   **Formalization Note** Lean's convention $x/0 = 0$ gives $g_1(0, v) = 0$; the paper uses $n \ge 1$ only.
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), (18), p. 15

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market

namespace OffPlatformThreats.Leakage

/-- **The fee function `g1`.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), (18), p. 15:
`g1(n, v) := (n v + cφ − cφ √(1 + n v/(cφ))) / n`, for `(n, v) ∈ ℝ²₊`.

By Lemma 2, `g1(n, v^j)` is the optimal on-platform fee with `n` providers on the platform and
`g1(1, v^j − Ro)` the optimal off-platform fee.

**Formalization Note.** Lean's `x / 0 = 0` gives `g1 m 0 v = 0`; the paper uses `g1` only at
`n ≥ 1`. -/
noncomputable def g1 (m : Market) (n v : ℝ) : ℝ :=
  (n * v + m.c * m.phi - m.c * m.phi * Real.sqrt (1 + n * v / (m.c * m.phi))) / n

end OffPlatformThreats.Leakage


