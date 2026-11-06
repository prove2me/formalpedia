-- Prove2me | Definitions.Def_MaxMinFracSched_pre
-- name    : MaxMinFracSched_pre
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:50.016265+00:00
-- url     : https://prove2.me/theorems/b6ef6513-9968-4289-99ce-cdc4364e579d
-- title:
--   The prefix instance $J_{\le t}$
-- statement:
--   For an instance $J$ and a time $t$,
--   $$J_{\le t}=\{\,i\in J : a_i\le t\,\},$$
--   the jobs released by time $t$ (jobs arriving exactly at $t$ included). It is what an online scheduler knows at time $t$.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 3, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job

namespace MaxMinFracSched

/-- **The prefix instance `J≤t`.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 3, p.12 (PDF p.14): "Let J≤t ⊆ J be the set of
jobs in J with arrival time at most t."

`pre J t` is the set of jobs of `J` with `a ≤ t` (jobs arriving exactly at `t` are included). -/
noncomputable def pre (J : Finset Job) (t : ℝ) : Finset Job :=
  J.filter (fun j => j.a ≤ t)

end MaxMinFracSched


