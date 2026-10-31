-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_deficiency
-- name    : CombOpt_TutteBerge_Multigraph_deficiency
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:54.647919+00:00
-- url     : https://prove2.me/theorems/4b48ca77-1536-4891-b35b-a91bfe3f9995
-- title:
--   Deficiency $\mathrm{def}(G)$
-- statement:
--   The **deficiency** $\mathrm{def}(G)$ is the minimum number of $M$-exposed nodes over all matchings $M$ of $G$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 127 (PDF p. 135)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_IsMatching
import Definitions.Def_CombOpt_TutteBerge_Multigraph_exposedNodes

namespace CombOpt.TutteBerge

/-- **The deficiency def(G).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 127 (PDF p. 135): "by def(G) (the 'deficiency of G') the minimum number of exposed
nodes for any matching of G."

**Formalization Note.** The infimum is taken in `ℕ` over a nonempty set (`∅` is a matching), so it
is attained. With `[Finite V]`, as in every theorem here, `Set.ncard` counts the exposed nodes
exactly. -/
noncomputable def Multigraph.deficiency {V E : Type*} (G : Multigraph V E) : ℕ :=
  sInf {n : ℕ | ∃ M : Set E, G.IsMatching M ∧ (G.exposedNodes M).ncard = n}

end CombOpt.TutteBerge


