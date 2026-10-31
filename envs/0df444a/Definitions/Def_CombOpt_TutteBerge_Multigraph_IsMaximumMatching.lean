-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_IsMaximumMatching
-- name    : CombOpt_TutteBerge_Multigraph_IsMaximumMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:05.807982+00:00
-- url     : https://prove2.me/theorems/b57177cb-95b6-424e-9aa1-5d72c4e95a65
-- title:
--   Maximum matching
-- statement:
--   A **maximum matching** of $G$ is a matching $M$ with $|N|\le |M|$ for every matching $N$ of $G$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 127 (PDF p. 135)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_IsMatching

namespace CombOpt.TutteBerge

/-- **A maximum matching.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 127 (PDF p. 135): "A *maximum* matching is one of maximum cardinality".

**Formalization Note.** `Set.ncard` is the true cardinality here because the edge set is finite in
every theorem that uses this definition (`[Finite E]`). -/
def Multigraph.IsMaximumMatching {V E : Type*} (G : Multigraph V E) (M : Set E) : Prop :=
  G.IsMatching M ∧ ∀ N : Set E, G.IsMatching N → N.ncard ≤ M.ncard

end CombOpt.TutteBerge


