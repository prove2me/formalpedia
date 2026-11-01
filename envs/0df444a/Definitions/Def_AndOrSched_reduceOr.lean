-- Prove2me | Definitions.Def_AndOrSched_reduceOr
-- name    : AndOrSched_reduceOr
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:28:50.311799+00:00
-- url     : https://prove2.me/theorems/5ae288ea-877f-4aa2-9c36-8c502568ec81
-- title:
--   The instance with redundant OR-arcs removed
-- statement:
--   The instance obtained by deleting every redundant OR-arc: same jobs, processing times, weights and AND-arcs; $b$'s OR-predecessors are its non-redundant OR-predecessors.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §1, p.4, "Otherwise we could remove the arc (a, b) from E∨"

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_nonRedPred
open scoped Classical NNReal

namespace AndOrSched

/-- The instance with every redundant OR-arc removed (Happach, Schulz, arXiv:2001.07011v1, §1, p.4, "Otherwise we could remove
the arc (a, b) from E∨"): same jobs, processing times, weights and AND-arcs, and OR-arcs
`(a, b)` exactly for `a ∈ nonRedPred I b`. -/
noncomputable def reduceOr (I : Instance) : Instance :=
  { I with orArc := fun a b => a ∈ nonRedPred I b }

end AndOrSched


