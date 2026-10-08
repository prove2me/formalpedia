-- Prove2me | Definitions.Def_SnarkGen_CycleCover_IsCycleEdges
-- name    : SnarkGen_CycleCover_IsCycleEdges
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:18.337499+00:00
-- url     : https://prove2.me/theorems/82986ea3-c49b-4c56-8be0-615b2628535f
-- title:
--   Cycle of a graph, as a set of edges (Section 2)
-- statement:
--   A **cycle** is a $2$-regular connected graph. A cycle of a finite simple graph $G$ is recorded here by its set of edges: a finite set $C \subseteq E(G)$ is a cycle of $G$ when there are distinct vertices $v_1,\dots,v_\ell$, $\ell \ge 3$, with $v_1v_2, v_2v_3, \dots, v_{\ell-1}v_\ell, v_\ell v_1 \in E(G)$ and
--
--   $$C = \{v_1v_2,\ v_2v_3,\ \dots,\ v_{\ell-1}v_\ell,\ v_\ell v_1\}.$$
--
--   The **length** of the cycle is $|C| = \ell$, its number of edges, which equals its number of vertices. Cycles are the building blocks of cycle double covers (Section 5) and cycle covers (Section 7).
--
--   **Formalization Note** `IsCycleEdges G C` says that `C` is the edge set (`Walk.edges.toFinset`) of a closed walk of `G` satisfying Mathlib's `Walk.IsCycle` (length at least $3$, no repeated edge, no repeated vertex other than the base point). Edges are unordered pairs `Sym2 V`.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 4, Section 2

import Mathlib

namespace SnarkGen.CycleCover

/-- arXiv:1206.6690v3, p. 4: a *cycle* is a 2-regular connected graph. A cycle of `G` is
recorded by its edge set: `C` is the set of edges of some closed walk of `G` that is a cycle
(`SimpleGraph.Walk.IsCycle`: length at least 3, no repeated vertex apart from the endpoints).
Its length is `C.card`. -/
def IsCycleEdges {V : Type*} [DecidableEq V] (G : SimpleGraph V) (C : Finset (Sym2 V)) : Prop :=
  ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.edges.toFinset = C

end SnarkGen.CycleCover


