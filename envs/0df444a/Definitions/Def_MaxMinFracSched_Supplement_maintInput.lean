-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_maintInput
-- name    : MaxMinFracSched_Supplement_maintInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:20:17.685211+00:00
-- url     : https://prove2.me/theorems/705e67f0-ea78-4152-92d1-cd31777b2ac7
-- title:
--   Input of one batch for the online maintenance of $\rho^\star$
-- statement:
--   A batch of $k$ jobs $j_1,\dots,j_k$ with common arrival time $a$ is given to the maintenance algorithm of Theorem 8.1 as the list of reals
--   $$
--   [\,a,\ d_{j_1},\ w_{j_1},\ \dots,\ d_{j_k},\ w_{j_k}\,].
--   $$
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Theorem 8.1, p.40 (PDF p.42); Section 8.1.6, p.49 (PDF p.51)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job

namespace MaxMinFracSched

namespace Supplement

/-- **The input of one batch for the online maintenance of `ρ⋆`.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Theorem 8.1, p.40 (PDF p.42): "A batch of k ≥ 1 jobs arriving at a common time";
Section 8.1.6, p.49 (PDF p.51): "Suppose k ≥ 1 jobs arrive at time a".

The batch `B = [j₁, …, j_k]` with common arrival time `a` is given as the reals
`[a, d_{j₁}, w_{j₁}, …, d_{j_k}, w_{j_k}]`. -/
noncomputable def maintInput (B : List Job) : List ℝ :=
  (B.head?.map Job.a).getD 0 :: B.flatMap (fun j => [j.d, j.w])

end Supplement

end MaxMinFracSched


