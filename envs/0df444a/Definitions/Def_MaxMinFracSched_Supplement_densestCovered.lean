-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_densestCovered
-- name    : MaxMinFracSched_Supplement_densestCovered
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:14:16.127346+00:00
-- url     : https://prove2.me/theorems/c9d65851-8b35-4bc7-80f3-42229f345281
-- title:
--   Jobs inside densest intervals, $S_J(I^{\star})$
-- statement:
--   $S_J(I^{\star})$ is the set of jobs $j\in J$ whose window $[a_j,d_j]$ is contained in some densest interval $[L,R]$ of $J$.
--
--   **Formalization Note** The paper's $I^{\star}$ is the set of maximal densest intervals: overlapping densest intervals are merged (proof of Theorem 7.3). Their union is again densest, and every densest interval lies in a maximal one, so containment in some densest interval is the same condition.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Theorem 7.3, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_Supplement_IsDensestInterval

namespace MaxMinFracSched

namespace Supplement

open Classical in
/-- **The jobs inside densest intervals, `S_J(I⋆)`.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Theorem 7.3, p.34 (PDF p.36): "let SJ(I⋆) := {i ∈ J : the job i is fully contained in
some I ∈ I⋆} be the set of jobs fully contained in these densest intervals".

The jobs `j ∈ J` with `[a_j, d_j] ⊆ [L, R]` for some densest interval `[L, R]`.

**Formalization Note.** The paper's `I⋆` consists of the maximal densest intervals (proof of
Theorem 7.3: overlapping ones "would be merged"); every densest interval lies in a maximal one, so
containment in some densest interval is the same condition. -/
noncomputable def densestCovered (J : Finset Job) : Finset Job :=
  J.filter (fun j => ∃ L R : ℝ, IsDensestInterval J L R ∧ L ≤ j.a ∧ j.d ≤ R)

end Supplement

end MaxMinFracSched


