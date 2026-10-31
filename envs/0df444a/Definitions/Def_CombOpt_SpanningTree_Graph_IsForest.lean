-- Prove2me | Definitions.Def_CombOpt_SpanningTree_Graph_IsForest
-- name    : CombOpt_SpanningTree_Graph_IsForest
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:18.811454+00:00
-- url     : https://prove2.me/theorems/a7491b35-90c8-42b8-9fd8-03dffe945568
-- title:
--   The spanning subgraph $(V,F)$ is a forest
-- statement:
--   The spanning subgraph $(V,F)$ is a **forest** if it has no circuit, that is, no circuit of $G$ has all its edges in $F$.
--
--   Since a loop is a circuit and two parallel edges form one, a forest contains no loop and no pair of parallel edges.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 11 (PDF p. 20)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_IsCircuit

namespace CombOpt.SpanningTree

/-- **The spanning subgraph (V, F) is a forest.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 11 (PDF p. 20): "A graph having no circuit is called a forest".

`G.IsForest F` says that the spanning subgraph `(V, F)` has no circuit: there is no circuit of `G`
all of whose edges lie in `F`.

**Formalization Note.** A circuit of the subgraph `(V, F)` is a circuit of `G` using only edges of
`F`. Since a loop is a circuit and two parallel edges form one, a forest contains no loop and no
two parallel edges. -/
def Graph.IsForest {V E : Type*} (G : Graph V E) (F : Finset E) : Prop :=
  ¬ ∃ (v : V) (p : G.Walk v v), G.IsCircuit p ∧ ∀ e ∈ p.edges, e ∈ F

end CombOpt.SpanningTree


