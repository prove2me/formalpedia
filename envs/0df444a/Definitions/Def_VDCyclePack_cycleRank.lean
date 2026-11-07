-- Prove2me | Definitions.Def_VDCyclePack_cycleRank
-- name    : VDCyclePack_cycleRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:12.212827+00:00
-- url     : https://prove2.me/theorems/13e35d09-06c0-4a9f-8e37-7f2e942ebfdc
-- title:
--   Cycle rank $\beta(F)$: the minimum size of a feedback edge set
-- statement:
--   A **feedback edge set** of a graph $F$ is a set $D\subseteq E(F)$ such that $F-D$ (all vertices kept) is a forest. The **cycle rank** $\beta(F)$ is the minimum size of a feedback edge set; the paper notes $\beta(F)=|E(F)|-|V(F)|+\kappa(F)$.
--
--   $\beta$ of unions of cycles is the structural quantity bounded in Theorem 4.2's hypothesis, Lemma 4.3 and Lemma 6.6, and charged in Lemma 5.1.
--
--   **Formalization Note** For a subgraph $F$ of $G$, $\beta(F)$ is the least $k$ such that some $k$ edges of $F$ leave an acyclic graph on all of $V(F)$. The formula $|E|-|V|+\kappa$ is a theorem in the paper, not the definition, which avoids natural-number subtraction. The union $\bigcup_{C\in R}C$ of a family is its supremum in the subgraph lattice (vertex sets and edge sets united, p.9).
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Section 3, p.10

import Mathlib

namespace VDCyclePack

/-- **Cycle rank β(F): the minimum size of a feedback edge set.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Section 3, p.10: "A feedback edge set of a graph or multigraph F is a set of edges
whose deletion leaves a forest. Its minimum size is the cycle rank β(F) = |E(F)| − |V(F)| + κ(F)."
p.9: "For D ⊆ E(F), the graph F − D retains all vertices and deletes only the edges in D."

For a subgraph `F` of `G`, `cycleRank F` is the least `k` such that some set `D` of `k` edges of `F`
leaves an acyclic graph when deleted from `F` (all vertices kept).

**Formalization Note.** β is defined as the minimum size of a feedback edge set; the formula
`|E| − |V| + κ` is an identity stated in the paper (p.10), not the definition. The vertex type is finite, so `D = E(F)` is a feedback edge set and
the infimum is a minimum. Unions `⋃_{C∈R} C` are `R.sup id` in the subgraph lattice (vertex sets
and edge sets united). -/
noncomputable def cycleRank {V : Type*} [Fintype V] {G : SimpleGraph V} (F : G.Subgraph) : ℕ :=
  sInf {k | ∃ D : Finset (Sym2 V), (↑D : Set (Sym2 V)) ⊆ F.edgeSet ∧ D.card = k ∧
    (F.deleteEdges (↑D : Set (Sym2 V))).coe.IsAcyclic}

end VDCyclePack


