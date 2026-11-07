-- Prove2me | Definitions.Def_DynHaussler_QCount
-- name    : DynHaussler_QCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:35:30.489308+00:00
-- url     : https://prove2.me/theorems/70a506d2-ad52-42f4-a1f5-04d2ba58acb3
-- title:
--   Schedule count $Q_r(m)=\sum_{i=0}^r n_i(m)$
-- statement:
--   For integers $r,m\ge0$,
--   $$
--   Q_r(m)=\sum_{i=0}^{r} n_i(m),
--   $$
--   the number of correction schedules of depth at most $r$ with ordinals in $[m]$, counting invalid, never-born and duplicate schedules. It bounds the size of the pointwise schedule cover of Lemma 13.
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Eq. (35), p.20 (PDF p.22)

import Mathlib
import Definitions.Def_DynHaussler_nCount

set_option autoImplicit false

namespace DynHaussler

/-- The number `Q_r(m) = ∑_{i=0}^r n_i(m)` of correction schedules of depth at most `r` with
ordinals in `[m]`.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Eq. (35), p.20 (PDF p.22). -/
def QCount (r m : ℕ) : ℕ := ∑ i ∈ Finset.range (r + 1), nCount i m

end DynHaussler


