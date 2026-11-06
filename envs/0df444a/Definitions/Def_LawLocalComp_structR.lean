-- Prove2me | Definitions.Def_LawLocalComp_structR
-- name    : LawLocalComp_structR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:10:56.150175+00:00
-- url     : https://prove2.me/theorems/6ce91f04-4521-4fbb-9ba1-3029ad5a989f
-- title:
--   Truncation level $r$ of Proposition 7.3
-- statement:
--   With $\delta=\varepsilon/4$ and $r_N=\lceil\log_2(N/\delta)\rceil$: $r=r_N$ under a horizon $N$; $r=2\lceil\log_2(12q/\delta)\rceil$ under a rank promise $q$ alone; $r=\min\{r_N,2\lceil\log_2(12q/\delta)\rceil\}$ under both.
--
--   **Formalization Note** The paper's "otherwise" covers both a rank-only and a two-resource call; with a rank promise alone there is no $r_N$, so only the rank term applies.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Proposition 7.3, p.13

import Mathlib
import Definitions.Def_LawLocalComp_Resource

namespace LawLocalComp

/-- **The truncation level `r` of Proposition 7.3.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Proposition 7.3, p.13 ("set δ = ε/4, ρ = 1 + δ, and rN = ⌈log2(N/δ)⌉. Use r = rN without a rank
promise, and otherwise r = min{rN, 2⌈log2(12q/δ)⌉}").

With `δ = ε/4`: `r = ⌈log₂(N/δ)⌉` under a horizon, `2⌈log₂(12q/δ)⌉` under a rank promise alone, and the
minimum of the two under both.

**Formalization Note.** "Otherwise" covers a rank-only and a two-resource call; with rank only there is
no `r_N`, so only the rank term applies (a reading). -/
noncomputable def structR (ε : ℚ) : Resource → ℕ
  | .horizon N => ⌈Real.logb 2 (N / ((ε : ℝ) / 4))⌉₊
  | .rank q => 2 * ⌈Real.logb 2 (12 * q / ((ε : ℝ) / 4))⌉₊
  | .both N q => min ⌈Real.logb 2 (N / ((ε : ℝ) / 4))⌉₊ (2 * ⌈Real.logb 2 (12 * q / ((ε : ℝ) / 4))⌉₊)

end LawLocalComp


