-- Prove2me | Definitions.Def_CombOpt_HeldKarp_Graph_IsForest
-- name    : CombOpt_HeldKarp_Graph_IsForest
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:39.590116+00:00
-- url     : https://prove2.me/theorems/d19ca14c-a408-4b29-923d-914ff7230fea
-- title:
--   Forest (edge set without a circuit)
-- statement:
--   A set $F\subseteq E$ of edges is a **forest** of $G$ if no circuit of $G$ has all its edges in $F$, i.e. the subgraph $(V,F)$ has no circuit.
--
--   In particular a forest contains no loop and no two parallel edges. Forests are the objects of the forest polytope (Theorem 8.8).
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 11 (PDF p. 20); §8.1, p. 280 (PDF p. 287)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_IsCircuit

namespace CombOpt.HeldKarp

/-- **The edge set F forms a forest.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 11
(PDF p. 20): "A graph having no circuit is called a forest"; a forest of G (§8.1, p. 280) is a
forest subgraph, identified with its edge set.

`G.IsForest F` says that there is no circuit of `G` all of whose edges lie in `F`.

**Formalization Note.** A forest of `G` is recorded by its edge set `F ⊆ E` (its characteristic
vector depends only on `F`). Since a loop is a circuit and two parallel edges form one, a forest
contains no loop and no two parallel edges. -/
def Graph.IsForest {V E : Type*} (G : Graph V E) (F : Finset E) : Prop :=
  ¬ ∃ (v : V) (p : G.Walk v v), G.IsCircuit p ∧ ∀ e ∈ p.edges, e ∈ F

end CombOpt.HeldKarp


