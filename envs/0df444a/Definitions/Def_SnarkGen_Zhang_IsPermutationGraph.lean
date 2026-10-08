-- Prove2me | Definitions.Def_SnarkGen_Zhang_IsPermutationGraph
-- name    : SnarkGen_Zhang_IsPermutationGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:20.85715+00:00
-- url     : https://prove2.me/theorems/77b7ae9d-c55d-457d-bbb0-45acdab7d0cb
-- title:
--   Permutation graphs: cubic graphs with a 2-factor of two induced cycles (Section 4.2)
-- statement:
--   A **cycle** is a $2$-regular connected graph. A cubic graph $G$ is a **permutation graph** if it has a $2$-factor that consists of two induced cycles. (These graphs have also been called cycle permutation graphs and generalized prisms.) A cubic graph is called a **permutation snark** if it is both a snark and a permutation graph.
--
--   The definition is stated through the vertex partition: $G$ is a permutation graph when $G$ is cubic and there is a set $A$ of vertices such that both induced subgraphs
--   $$
--   G[A] \quad\text{and}\quad G[V \setminus A]
--   $$
--   are cycles, i.e. connected and $2$-regular. This is equivalent to the paper's wording. If $G[A]$ and $G[V\setminus A]$ are cycles, their union is a spanning $2$-regular subgraph, a $2$-factor, whose two components are induced cycles. Conversely, the vertex sets of the two cycles of such a $2$-factor give $A$ and $V \setminus A$, and an induced cycle has no chords, so the induced subgraphs are exactly the two cycles. In a permutation graph the edges not on the two cycles form a perfect matching between them, so the two cycles have the same length.
--
--   The Petersen graph is a permutation graph: its outer $5$-cycle and inner pentagram are induced cycles.
--
--   **Formalization Note** `IsCycleGraph H` is `H.Connected ∧ H.IsRegularOfDegree 2` for a finite graph $H$; Mathlib's `Connected` includes nonemptiness, so both cycles are nonempty. The induced subgraphs are `G.induce A` and `G.induce Aᶜ`, on the subtypes of $A$ and its complement. Degrees and finiteness of the subtypes use classical decidability.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 8, Section 4.2 (definition of permutation graph); p. 4, Section 2 (definition of cycle and 2-factor)

import Mathlib

namespace SnarkGen.Zhang

open Classical in
/-- A *cycle* (p. 4): a 2-regular connected graph (finite here; `Connected` includes
nonemptiness). -/
def IsCycleGraph {W : Type*} [Fintype W] (H : SimpleGraph W) : Prop :=
  H.Connected ∧ H.IsRegularOfDegree 2

open Classical in
/-- A *permutation graph* (p. 8): a cubic graph with a 2-factor consisting of two induced
cycles. Equivalently, the vertex set splits as `A ∪ Aᶜ` so that the induced subgraphs
`G[A]` and `G[Aᶜ]` are both cycles. -/
def IsPermutationGraph {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  G.IsRegularOfDegree 3 ∧
    ∃ A : Set V, IsCycleGraph (G.induce A) ∧ IsCycleGraph (G.induce Aᶜ)

end SnarkGen.Zhang


