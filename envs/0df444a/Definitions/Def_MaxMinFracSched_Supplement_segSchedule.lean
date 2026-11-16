-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_segSchedule
-- name    : MaxMinFracSched_Supplement_segSchedule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:22:39.678136+00:00
-- url     : https://prove2.me/theorems/fdf931f2-0f1a-4c27-86f5-8aba5f66123d
-- title:
--   Schedule assembled from a scheduler's decisions
-- statement:
--   For decisions $(t_1,s_1),\dots,(t_m,s_m)$, job $j$ is processed at rate $1$ at time $x$ when some decision $i$ serves $j$ and $t_i\le x<t_{i+1}$ (with no upper limit for the last decision). Otherwise its rate is $0$.
--
--   On each interval between consecutive events the scheduler serves one fixed job or idles (proof of Lemma 5.6), and this is the schedule it produces.
--
--   **Formalization Note** The rates are summed over the decisions. Decisions whose times decrease therefore produce overlapping rates, which no feasible schedule and no run allows.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Lemma 5.6 (proof), p.26 (PDF p.28)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job

namespace MaxMinFracSched

namespace Supplement

open Classical in
/-- **The schedule assembled from a scheduler's decisions.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Lemma 5.6 proof, p.26 (PDF p.28): "On each open interval between consecutive events, each
run serves one fixed job or idles".

For decisions `segs = [(t₁, s₁), …, (t_m, s_m)]`, job `j` has rate `1` at time `x` when some
decision `i` serves `j` (`s_i = some j`) and `t_i ≤ x` and `x < t_{i+1}` (no upper limit for the last
decision); otherwise its rate is `0`.

**Formalization Note.** The rates are summed over the decisions, so decisions whose times are not
nondecreasing produce rates that are not `{0, 1}`-valued or a processor sum above `1`, which no
feasible schedule or run allows. -/
noncomputable def segSchedule (segs : List (ℝ × Option Job)) : Job → ℝ → ℝ :=
  fun j x => ∑ i : Fin segs.length,
    if segs[i].2 = some j ∧ segs[i].1 ≤ x ∧ (∀ p ∈ segs[i.1 + 1]?, x < p.1) then 1 else 0

end Supplement

end MaxMinFracSched


