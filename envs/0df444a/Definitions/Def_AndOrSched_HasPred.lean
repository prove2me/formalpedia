-- Prove2me | Definitions.Def_AndOrSched_HasPred
-- name    : AndOrSched_HasPred
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:28:11.371125+00:00
-- url     : https://prove2.me/theorems/96e6687c-0e70-49b2-91c9-ee85026b444e
-- title:
--   Jobs with a predecessor
-- statement:
--   A job $j$ **has a predecessor** if it has an AND-predecessor, or if $j=b\in B$ and $\mathcal P(b)\neq\emptyset$.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.6, "every job j ∈ N that has no predecessors"

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_andRel
import Definitions.Def_AndOrSched_orPred
open scoped Classical NNReal

namespace AndOrSched

/-- Job `j` has a predecessor (Happach, Schulz, arXiv:2001.07011v1, §2, p.6, "every job j ∈ N that has no predecessors"): an
AND-predecessor, or, for `j = b ∈ B`, a nonempty set `𝒫(b)` of OR-predecessors. -/
def HasPred (I : Instance) (j : I.N) : Prop :=
  (∃ i, andRel I i j) ∨ ∃ b, j = Sum.inr b ∧ (orPred I b).Nonempty

end AndOrSched


