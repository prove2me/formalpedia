-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_IsInessential
-- name    : CombOpt_TutteBerge_Multigraph_IsInessential
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:24.115171+00:00
-- url     : https://prove2.me/theorems/b413e05b-df95-478c-9fae-ba8913437faf
-- title:
--   Inessential node
-- statement:
--   A node $v$ of $G$ is **inessential** if there is a maximum matching of $G$ not covering $v$; otherwise $v$ is **essential**.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 132 (PDF p. 140)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_IsMaximumMatching
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Covers

namespace CombOpt.TutteBerge

/-- **An inessential node.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 132 (PDF p. 140): "Let us call a node v of G *inessential* if there is a maximum
matching of G not covering v; otherwise, we call v *essential*." -/
def Multigraph.IsInessential {V E : Type*} (G : Multigraph V E) (v : V) : Prop :=
  ∃ M : Set E, G.IsMaximumMatching M ∧ ¬ G.Covers M v

end CombOpt.TutteBerge


