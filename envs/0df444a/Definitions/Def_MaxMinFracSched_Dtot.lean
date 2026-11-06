-- Prove2me | Definitions.Def_MaxMinFracSched_Dtot
-- name    : MaxMinFracSched_Dtot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:21:35.062833+00:00
-- url     : https://prove2.me/theorems/806bbc8c-8150-438f-be80-1ab9c479e7e3
-- title:
--   Hard family: total work $D_i$ due at $t_i$
-- statement:
--   The total work due at $t_i$ in the hard family,
--   $$D_i=\sum_{m=0}^{i-1} w_m(i)\qquad(1\le i\le k).$$
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 6.3, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_MaxMinFracSched_hw

namespace MaxMinFracSched

/-- **The total work `D_i` due at `t_i`.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 6.3, p.31 (PDF p.33): "let Di denote the
total work due at ti, for 1 ≤ i ≤ k. Then Di = Σ_{j=0}^{i−1} wj(i)".

`Dtot x k i = Σ_{m=0}^{i−1} w_m(i)` (with the works of the corrected display (10), `hw`). -/
noncomputable def Dtot (x : ℝ) (k i : ℕ) : ℝ :=
  ∑ m ∈ Finset.range i, hw x k m i

end MaxMinFracSched


