-- Prove2me | Definitions.Def_AndOrSched_outSched
-- name    : AndOrSched_outSched
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:16.514258+00:00
-- url     : https://prove2.me/theorems/57eaa8bb-c3e5-4695-98ba-4a5f2cb3a36d
-- title:
--   The schedule returned for the original instance
-- statement:
--   Given an order $\prec$ of the jobs of the normalized instance $I'$, the schedule returned for $I$: the jobs of $Z$ complete at time $0$, and every other job $j$ completes at $C'_j/D$, where $C'$ is the schedule of $\prec$ in $I'$ (the dummies take no time and are dropped, and the scaling by $D$ is undone).
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.6

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_scaleD
import Definitions.Def_AndOrSched_normalize
import Definitions.Def_AndOrSched_toNorm
import Definitions.Def_AndOrSched_listC
open scoped Classical NNReal

namespace AndOrSched

/-- The schedule that the algorithm returns for the original instance `I`, given the order `σ` of the
jobs of the normalized instance `normalize I` (Happach, Schulz, arXiv:2001.07011v1, §2, p.6): the disregarded jobs of `Z` complete
at time `0`, and the other jobs are processed in the order `σ` without idle time; the dummy jobs are
dropped and the scaling by `D` is undone.

**Formalization Note** Since dummies and jobs of `Z` take no time, a job `j ∉ Z` completes at
`C'ⱼ / D`, where `C'` is the schedule of `σ` in `normalize I` (`listC`) and `D = scaleD I`. -/
noncomputable def outSched (I : Instance)
    (σ : (normalize I).N ≃ Fin (Fintype.card (normalize I).N)) (j : I.N) : ℝ :=
  match toNorm I j with
  | none => 0
  | some j' => listC (normalize I) σ j' / (scaleD I : ℝ)

end AndOrSched


