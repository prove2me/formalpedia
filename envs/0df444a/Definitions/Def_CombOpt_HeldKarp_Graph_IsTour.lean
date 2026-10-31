-- Prove2me | Definitions.Def_CombOpt_HeldKarp_Graph_IsTour
-- name    : CombOpt_HeldKarp_Graph_IsTour
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:31.078826+00:00
-- url     : https://prove2.me/theorems/fb57f0da-9b60-4208-a225-a2d41219e9fe
-- title:
--   Tour (Hamiltonian circuit)
-- statement:
--   A **tour** of $G$ is a circuit of $G$ that meets every node; it is recorded by its edge set $T\subseteq E$, and its cost is $c(T)=\sum_{e\in T}c_e$.
--
--   On two nodes, two parallel edges form a tour; on one node, a loop is a tour. The **traveling salesman problem** on $G$ asks for a tour of minimum cost.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §7.1, p. 241 (PDF p. 249)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_IsCircuit

namespace CombOpt.HeldKarp

/-- **A tour (Hamiltonian circuit).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §7.1, p. 241
(PDF p. 249): "A tour is then a circuit in G that meets every node. In this context, tours are
sometimes called Hamiltonian circuits."

`G.IsTour T` says that `T` is the edge set of a circuit of `G` whose node terms include every node.

**Formalization Note.** A tour is recorded by its edge set, which is what its cost `Σ_{e ∈ T} c_e`
depends on. "Circuit" is the book's notion (`Graph.IsCircuit`), so on two nodes a pair of parallel
edges is a tour and on one node a loop is a tour. -/
def Graph.IsTour {V E : Type*} [DecidableEq E] (G : Graph V E) (T : Finset E) : Prop :=
  ∃ (v : V) (p : G.Walk v v), G.IsCircuit p ∧ (∀ u : V, u ∈ p.support) ∧ T = p.edges.toFinset

end CombOpt.HeldKarp


