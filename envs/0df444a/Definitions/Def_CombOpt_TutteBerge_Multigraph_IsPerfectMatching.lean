-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_IsPerfectMatching
-- name    : CombOpt_TutteBerge_Multigraph_IsPerfectMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:11.523589+00:00
-- url     : https://prove2.me/theorems/7b32ff80-9455-473f-8ddd-2f67cf1d5e6d
-- title:
--   Perfect matching
-- statement:
--   A **perfect matching** of $G$ is a matching that covers every node of $G$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 127 (PDF p. 135)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_IsMatching
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Covers

namespace CombOpt.TutteBerge

/-- **A perfect matching.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 127 (PDF p. 135): "A *perfect* matching is one that covers all the nodes." -/
def Multigraph.IsPerfectMatching {V E : Type*} (G : Multigraph V E) (M : Set E) : Prop :=
  G.IsMatching M ∧ ∀ v : V, G.Covers M v

end CombOpt.TutteBerge


