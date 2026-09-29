-- Prove2me | Definitions.Def_ChvatalPolytopes_Neighbors_IsBicoloration
-- name    : ChvatalPolytopes_Neighbors_IsBicoloration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:21:10.520977+00:00
-- url     : https://prove2.me/theorems/6385066a-6892-4767-b63d-c55a78c34dd7
-- title:
--   Bicoloration of a graph (Lemma 6.1)
-- statement:
--   Let $T=(V,E)$ be a finite graph. A **bicoloration** $V=B\cup R$ of $T$ is a partition of the vertex set into two disjoint sets $B$ and $R$,
--   $$B\cup R=V,\qquad B\cap R=\emptyset,$$
--   such that every edge of $T$ joins a vertex of $B$ to a vertex of $R$.
--
--   Every tree has a bicoloration, unique up to swapping $B$ and $R$; Lemma 6.1 constructs a weighting of a tree whose maximizers over the stable sets are exactly the two colour classes.
--
--   **Formalization Note** $B$ and $R$ are finsets of the finite vertex type; either may be empty (for a graph with one vertex).
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 149, Lemma 6.1 (bicoloration)

import Mathlib

namespace ChvatalPolytopes.Neighbors

/-- A **bicoloration** `V = B ∪ R` of a graph `T` on `V` (Chvátal 1975, p. 149, Lemma 6.1):
a partition of the vertex set into two disjoint parts `B` and `R` such that every edge of `T`
joins a vertex of `B` to a vertex of `R`. -/
def IsBicoloration {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V)
    (B R : Finset V) : Prop :=
  Disjoint B R ∧ B ∪ R = Finset.univ ∧
    ∀ u v, T.Adj u v → (u ∈ B ∧ v ∈ R) ∨ (u ∈ R ∧ v ∈ B)

end ChvatalPolytopes.Neighbors


