-- Prove2me | Definitions.Def_erdos81_clique_partitions
-- name    : erdos81_clique_partitions
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-08T05:05:21.080858+00:00
-- url     : https://prove2.me/theorems/2e7d4362-3af7-49a3-b9a4-de8d47975b0d
-- title:
--   Chordal graphs and exact edge partitions into cliques
-- statement:
--   This module defines chordality through a perfect-elimination ranking: the later neighbors of every vertex are pairwise adjacent. For finite simple graphs, this is the standard chordal-graph characterization.
--
--   An exact edge-clique partition is a finite family of finite vertex sets, each spanning a complete subgraph, such that every graph edge belongs to exactly one family member. Pieces may share vertices but not edges. `HasCliquePartitionAtMost G B` asks for such a family whose natural-number cardinality, coerced to a real number, is at most $B$.
--
--   Edgeless and disconnected graphs are included. Empty or singleton listed cliques are not explicitly forbidden, but they cannot help satisfy an upper bound and contain no graph edge.
-- source:
--   Erdos Problems, Problem 81, https://www.erdosproblems.com/81; Erdős--Ordman--Zalcstein, Clique Partitions of Chordal Graphs, CPC 2(4) (1993), https://doi.org/10.1017/S0963548300000808

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

namespace Erdos81

universe u

/-- A finite set of vertices spans a complete subgraph. -/
def IsClique {V : Type u} (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ C → v ∈ C → u ≠ v → G.Adj u v

/-- A perfect-elimination presentation of a chordal graph. Later neighbors of
each vertex must be pairwise adjacent. -/
def IsChordal {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ rank : V → ℕ,
    Function.Injective rank ∧
    ∀ ⦃v a b : V⦄,
      G.Adj v a → G.Adj v b → rank v < rank a → rank v < rank b →
      a ≠ b → G.Adj a b

/-- An exact edge partition into complete subgraphs. Each graph edge occurs in
exactly one listed clique. -/
def IsEdgeCliquePartition {V : Type u} (G : SimpleGraph V)
    (P : Finset (Finset V)) : Prop :=
  (∀ C ∈ P, IsClique G C) ∧
  ∀ ⦃u v : V⦄, G.Adj u v →
    ∃! C : Finset V, C ∈ P ∧ u ∈ C ∧ v ∈ C

/-- `G` has an exact edge-clique partition with at most the real-valued bound
`B` pieces. -/
def HasCliquePartitionAtMost {V : Type u} (G : SimpleGraph V) (B : ℝ) : Prop :=
  ∃ P : Finset (Finset V),
    IsEdgeCliquePartition G P ∧ (P.card : ℝ) ≤ B

end Erdos81


