-- Prove2me | Definitions.Def_MaxMinFracSched_optAt
-- name    : MaxMinFracSched_optAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:21:48.88786+00:00
-- url     : https://prove2.me/theorems/3c5ab601-8679-4bcf-8cd5-cc497bb41b1b
-- title:
--   Running offline optimum $\hat f_J(t)$
-- statement:
--   For an instance $J$ and a time $t$,
--   $$\hat f_J(t)=\hat f_{J_{\le t}},$$
--   the offline optimum of the jobs released by time $t$, i.e. OPT's value if no further jobs arrived. It is non-increasing in $t$ and is the quantity ScaledEDF tracks online.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 3, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_pre
import Definitions.Def_MaxMinFracSched_optVal

namespace MaxMinFracSched

/-- **The running offline optimum `f̂_J(t)`.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 3, p.12 (PDF p.14): "we define
f̂J(t) := f̂J≤t, which is OPT's fractional completion if on J≤t; that is OPT's fractional
completion if no further jobs were released after this time."

`optAt J t = optVal (pre J t)`. -/
noncomputable def optAt (J : Finset Job) (t : ℝ) : ℝ :=
  optVal (pre J t)

end MaxMinFracSched


