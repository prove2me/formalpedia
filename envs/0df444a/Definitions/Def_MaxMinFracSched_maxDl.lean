-- Prove2me | Definitions.Def_MaxMinFracSched_maxDl
-- name    : MaxMinFracSched_maxDl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:51.281335+00:00
-- url     : https://prove2.me/theorems/8c3e4ad1-57f0-42e3-abec-3eccc53e07b3
-- title:
--   Final deadline $T$ of an instance
-- statement:
--   For a nonempty instance $J$, $T=\max_{i\in J} d_i$, the final deadline. It is set to $0$ for the empty instance, where it is never used.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 4.1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job

namespace MaxMinFracSched

/-- **The final deadline `T` of an instance.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 4.1, p.14 (PDF p.16): "recall that T
is the final deadline".

`maxDl J = max_{j∈J} d_j` for nonempty `J` (and `0` for `J = ∅`, never used). -/
noncomputable def maxDl (J : Finset Job) : ℝ :=
  if h : J.Nonempty then J.sup' h Job.d else 0

end MaxMinFracSched


