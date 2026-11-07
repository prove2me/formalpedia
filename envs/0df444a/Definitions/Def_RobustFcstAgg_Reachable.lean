-- Prove2me | Definitions.Def_RobustFcstAgg_Reachable
-- name    : RobustFcstAgg_Reachable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:41:09.872194+00:00
-- url     : https://prove2.me/theorems/eaafbb53-8999-40cc-9b7d-a6c3d32e1f9b
-- title:
--   Reachability among queries
-- statement:
--   $Q'$ is reachable from $Q$ if a directed path of queries leads from $Q$ to $Q'$. Each query is reachable from itself, so that $Q\in N^*_G(Q)$, as in the source.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 2.2, p.6

import Mathlib

namespace RobustFcstAgg

/-- **Reachability among queries.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 2.2, p.6: `Q′ ∈ N*_G(Q)`, "the set of reachable nodes from `Q`
in `G`, including `Q` itself". -/
def Reachable {ι : Type} (out : ι → Finset (Option ι)) (a b : ι) : Prop :=
  Relation.ReflTransGen (fun u v : ι => some v ∈ out u) a b

end RobustFcstAgg


