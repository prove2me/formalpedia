-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_matchingNumber
-- name    : CombOpt_TutteBerge_Multigraph_matchingNumber
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:55.908567+00:00
-- url     : https://prove2.me/theorems/49ba0ec9-cf49-4a14-926b-fe29b35f513a
-- title:
--   Matching number $\nu(G)$
-- statement:
--   The **matching number** $\nu(G)$ is the cardinality of a maximum matching of $G$.
--
--   **Formalization Note** It is the supremum in $\mathbb N$ of the sizes of the matchings of $G$. For finite $E$ the set of sizes is nonempty and bounded, so the supremum is attained.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 127 (PDF p. 135)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_IsMatching

namespace CombOpt.TutteBerge

/-- **The matching number ν(G).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 127 (PDF p. 135): "We denote by ν(G) the cardinality of a maximum matching of G".

**Formalization Note.** The supremum is taken in `ℕ` over the sizes of the matchings of `G`. That
set is nonempty (`∅` is a matching) and, when `E` is finite, bounded by `|E|`, so with
`[Finite E]`, as in every theorem here, the supremum is attained and is the size of a maximum
matching. -/
noncomputable def Multigraph.matchingNumber {V E : Type*} (G : Multigraph V E) : ℕ :=
  sSup {n : ℕ | ∃ M : Set E, G.IsMatching M ∧ M.ncard = n}

end CombOpt.TutteBerge


