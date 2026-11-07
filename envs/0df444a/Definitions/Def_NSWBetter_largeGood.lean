-- Prove2me | Definitions.Def_NSWBetter_largeGood
-- name    : NSWBetter_largeGood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:50:55.844202+00:00
-- url     : https://prove2.me/theorems/740d9324-d57d-4b1f-9a47-fc9550be1d51
-- title:
--   Large good $g_i$ received by agent $i<\ell$
-- statement:
--   For $i\le\ell$, agent $i$ receives exactly one large good in $W$, namely $g_i$; `largeGood s i` is its value $v(g_i)$ (0-based index).
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 3, p.13 (Properties C, D: agents i ∈ [ℓ] who receive a large good g_i)

import Mathlib
import Definitions.Def_NSWBetter_sortDesc

namespace NSWBetter

/-- **The large good of agent i.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 3, p.13, Properties C and D: agent `i ∈ [ℓ]` receives the large good `g_i`.

`largeGood s i = v(g_(i+1))`, the `i`-th (0-based) largest value; for `i < ℓ` it is the large good in agent `i`'s round-robin bundle. -/
noncomputable def largeGood (s : Multiset ℝ) (i : ℕ) : ℝ := (sortDesc s).getD i 0

end NSWBetter


