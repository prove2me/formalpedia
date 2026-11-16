-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_inputOrder
-- name    : MaxMinFracSched_Supplement_inputOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:23:01.303102+00:00
-- url     : https://prove2.me/theorems/dc7f43c9-49be-4156-93b7-36a87b6dad45
-- title:
--   Priority by deadline, ties broken by input position
-- statement:
--   For a presentation $L$ of an instance, job $j$ has priority over job $k$ when $d_j<d_k$, or when $d_j=d_k$ and $j$ comes before $k$ in $L$. This is the order $(d_i,i)$ of the scheduling tree in Section 8.1.7, "where the index breaks any deadline ties".
--
--   **Formalization Note** On the jobs of a duplicate-free list this is a strict total order that refines the deadline order.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 8.1.7, p.50 (PDF p.52); Section 8.1.8, p.51 (PDF p.53)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job

namespace MaxMinFracSched

namespace Supplement

/-- **Priority by deadline, ties by input position.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 8.1.7, "Scheduling bookkeeping", p.50 (PDF p.52): "we keep the unexpired jobs in a
separate balanced tree ordered by (di, i), where the index breaks any deadline ties"; Section 8.1.8,
p.51 (PDF p.53).

`inputOrder L j k`: `j` has an earlier deadline than `k`, or the same deadline and an earlier
position in the list `L`.

**Formalization Note.** On the jobs of a duplicate-free list `L` this is a strict total order that
refines the deadline order. -/
def inputOrder (L : List Job) (j k : Job) : Prop :=
  j.d < k.d ∨ (j.d = k.d ∧ L.idxOf j < L.idxOf k)

end Supplement

end MaxMinFracSched


