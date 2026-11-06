-- Prove2me | Definitions.Def_MaxMinFracSched_TT__4c2bff
-- name    : MaxMinFracSched_TT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:52.603744+00:00
-- url     : https://prove2.me/theorems/4c2bffd3-275b-49fd-8b5e-bff2cb416373
-- title:
--   Hard family: interval lengths $T_i$
-- statement:
--   The length of the $i$-th interval of the hard family,
--   $$T_i=t_i-t_{i-1}\qquad(1\le i\le k).$$
--   So $T_1=x^{k-1}$ and $T_i=t_i(1-x)$ for $i\ge2$.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 6.1, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_MaxMinFracSched_tt

namespace MaxMinFracSched

/-- **The interval lengths `Tᵢ` of the hard family.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 6.1, p.29 (PDF p.31): "Then
the ith interval lies between ti−1 and ti … Let Ti be the length of interval i".

`TT x k i = t_i − t_{i−1}` (used for `1 ≤ i ≤ k`). -/
noncomputable def TT (x : ℝ) (k i : ℕ) : ℝ :=
  tt x k i - tt x k (i - 1)

end MaxMinFracSched


