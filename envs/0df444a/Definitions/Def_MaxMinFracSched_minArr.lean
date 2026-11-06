-- Prove2me | Definitions.Def_MaxMinFracSched_minArr
-- name    : MaxMinFracSched_minArr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:59.155924+00:00
-- url     : https://prove2.me/theorems/9d80c669-7899-4e45-83b0-27d3ac008c97
-- title:
--   First arrival time of an instance
-- statement:
--   For a nonempty instance $J$, $\min_{i\in J} a_i$, the first arrival time (the start of the time horizon). It is set to $0$ for the empty instance, where it is never used.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 4, pp.15–16 (PDF pp.17–18)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job

namespace MaxMinFracSched

/-- **The first arrival time of an instance.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 4 (used in Lemmas 4.6–4.7,
pp.15–16): the start of the time horizon of an instance.

`minArr J = min_{j∈J} a_j` for nonempty `J` (and `0` for `J = ∅`, never used). -/
noncomputable def minArr (J : Finset Job) : ℝ :=
  if h : J.Nonempty then J.inf' h Job.a else 0

end MaxMinFracSched


