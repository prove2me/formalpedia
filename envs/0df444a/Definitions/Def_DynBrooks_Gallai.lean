-- Prove2me | Definitions.Def_DynBrooks_Gallai
-- name    : DynBrooks_Gallai
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:04:56.780478+00:00
-- url     : https://prove2.me/theorems/48837df4-0a9b-4e00-a05e-aa6592e55854
-- title:
--   §3 — blocks and Gallai trees
-- statement:
--   A **block** of a graph is a maximal connected subgraph without a cut vertex, with bridges and isolated vertices also regarded as blocks. Here a block is given by its vertex set $B$: $G[B]$ is connected, and removing any one vertex of $B$ leaves a connected graph or (if $|B|=1$) nothing; $B$ is maximal under inclusion with this property.
--
--   A connected graph is a **Gallai tree** if every block is a clique or an odd cycle (a cycle of odd length at least $3$).
--
--   By the degree-choosability theorem of Erdős, Rubin and Taylor and of Vizing, a connected graph is degree-choosable if and only if it is not a Gallai tree; Lemma 3.1 and the stopping test 2 of Algorithm 3 rest on this notion.
--
--   **Formalization Note** A maximal such vertex set induces the block, so describing blocks by vertex sets loses nothing. A triangle is both a clique and an odd cycle.
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), §3, p.14 (PDF 16)

import Mathlib

namespace DynBrooks

/-! # Blocks and Gallai trees

Mishra, Mukherjee, *Fully Dynamic Brooks Coloring* (STOC 2027 submission, sha256 6542a9f1…), §3,
p.14 (PDF 16): "More generally, a block is a maximal connected subgraph without a cut vertex, with
bridges and isolated vertices also regarded as blocks. A connected graph is a Gallai tree if every
block is a clique or an odd cycle."

**Formalization Note.** A subgraph is given by its vertex set: a maximal such subgraph is induced.
A one-vertex set has no cut vertex, and two adjacent vertices have none either, so bridges and
isolated vertices are blocks by the definition itself. A triangle is both a clique and an odd cycle. -/

/-- `B` spans a connected induced subgraph without a cut vertex: `B` is nonempty, `G[B]` is connected,
and removing any one vertex leaves a connected graph, or nothing at all. -/
def IsCutFree {V : Type} (G : SimpleGraph V) (B : Set V) : Prop :=
  B.Nonempty ∧ (G.induce B).Connected ∧
    (B.Subsingleton ∨ ∀ x ∈ B, (G.induce (B \ {x})).Connected)

/-- A **block** of `G`: an inclusion-maximal cut-free vertex set. -/
def IsBlock {V : Type} (G : SimpleGraph V) (B : Set V) : Prop :=
  IsCutFree G B ∧ ∀ B' : Set V, B ⊆ B' → IsCutFree G B' → B' = B

/-- `G[B]` is an odd cycle (of length at least `3`). -/
def IsOddCycleOn {V : Type} (G : SimpleGraph V) (B : Set V) : Prop :=
  ∃ k : ℕ, Nonempty (G.induce B ≃g SimpleGraph.cycleGraph (2 * k + 3))

/-- A **Gallai tree**: a connected graph in which every block is a clique or an odd cycle. -/
def IsGallaiTree {V : Type} (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ B : Set V, IsBlock G B → G.IsClique B ∨ IsOddCycleOn G B

end DynBrooks


