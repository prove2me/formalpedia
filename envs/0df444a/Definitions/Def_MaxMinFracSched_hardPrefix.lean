-- Prove2me | Definitions.Def_MaxMinFracSched_hardPrefix
-- name    : MaxMinFracSched_hardPrefix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:22:46.110287+00:00
-- url     : https://prove2.me/theorems/d6b2e642-6294-4b55-825e-aaa735c9d547
-- title:
--   Hard family: prefix instances $J^{(i)}$
-- statement:
--   For $1\le i\le k$, the instance
--   $$J^{(i)}=J_{<t_i}=\{\text{job released at } t_m \text{ and due at } t_j : 0\le m<i,\ m<j\le k\},$$
--   all jobs released at $t_0,\dots,t_{i-1}$. These are nested, $J^{(i)}\subset J^{(i')}$ for $i<i'$, and $J^{(k)}$ is the whole family.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 6.1, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_hardJob

namespace MaxMinFracSched

/-- **The prefix instances `J^{(i)}` of the hard family.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 6.1, p.29 (PDF p.31): "We
can view the instance family as the collection of instances J(i) := J<ti for 1 ≤ i ≤ k, so that
J(i) consists of all jobs in the sequence released at times t0, . . . , ti−1. (Note that
J(i) ⊂ J(i′) for i < i′.)"

`hardPrefix x k i` is the set of jobs `hardJob x k m j` with release index `m < i` and
`m < j ≤ k`. `hardPrefix x k k` is the whole family `J^{(k)}`. -/
noncomputable def hardPrefix (x : ℝ) (k i : ℕ) : Finset Job :=
  ((Finset.range i ×ˢ Finset.range (k + 1)).filter (fun p => p.1 < p.2)).image
    (fun p => hardJob x k p.1 p.2)

end MaxMinFracSched


