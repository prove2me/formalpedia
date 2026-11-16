-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_batches
-- name    : MaxMinFracSched_Supplement_batches
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:19:42.741628+00:00
-- url     : https://prove2.me/theorems/ebe74b52-83ba-4115-a8fa-a696427eae36
-- title:
--   Arrival batches of an instance
-- statement:
--   An instance is presented as a list $L$ of its jobs. Its **batches** are, for each distinct arrival time $a$ in increasing order, the list of the jobs of $L$ with arrival time $a$, in their order in $L$. Jobs are presented to an online algorithm batch by batch, and the **index** of a job is its position in the concatenation of the batches.
--
--   Section 8 processes jobs sharing an arrival time together as one batch.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 8.1, p.40 (PDF p.42)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job

namespace MaxMinFracSched

namespace Supplement

/-- **The arrival batches of an instance.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 8.1, p.40 (PDF p.42): "All three parameters of a job are revealed at its arrival, and jobs
sharing an arrival time are processed together as a single batch."

For an instance presented as the list `L` of its jobs, `batches L` lists, for each distinct arrival
time in increasing order, the jobs of `L` with that arrival time, in their order in `L`. The jobs
are presented to an online algorithm in the order of `(batches L).flatten`, and a job's position in
that list is its index. -/
noncomputable def batches (L : List Job) : List (List Job) :=
  ((L.map Job.a).toFinset.sort (· ≤ ·)).map (fun a => L.filter (fun j => decide (j.a = a)))

end Supplement

end MaxMinFracSched


