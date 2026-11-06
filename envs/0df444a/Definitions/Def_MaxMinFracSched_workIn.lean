-- Prove2me | Definitions.Def_MaxMinFracSched_workIn
-- name    : MaxMinFracSched_workIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:53.888879+00:00
-- url     : https://prove2.me/theorems/97ee3853-ac39-489e-9c47-9cfd31258ee4
-- title:
--   Interval work $W_J([L,R])$
-- statement:
--   For an instance $J$ and an interval $[L,R]$,
--   $$W_J([L,R])=\sum_{i\in J:\ L\le a_i\le d_i\le R} w_i,$$
--   the total work of the jobs whose arrival time and deadline both lie in $[L,R]$. All of this work must be done inside $[L,R]$.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Definition 3.1, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job

namespace MaxMinFracSched

/-- **The work `W_J([L, R])` of an interval.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Definition 3.1 (Work density), p.12
(PDF p.14): "For an instance J and an interval I = [L, R], define WJ(I) := Σ_{i∈J: L≤ai≤di≤R} wi".

The total work of the jobs whose arrival time and deadline both lie in `[L, R]`. -/
noncomputable def workIn (J : Finset Job) (L R : ℝ) : ℝ :=
  ∑ j ∈ J.filter (fun j => L ≤ j.a ∧ j.a ≤ j.d ∧ j.d ≤ R), j.w

end MaxMinFracSched


