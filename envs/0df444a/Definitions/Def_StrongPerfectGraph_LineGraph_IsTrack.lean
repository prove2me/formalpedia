-- Prove2me | Definitions.Def_StrongPerfectGraph_LineGraph_IsTrack
-- name    : StrongPerfectGraph_LineGraph_IsTrack
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:18:29.554997+00:00
-- url     : https://prove2.me/theorems/b263bba8-ab57-4f5a-9e14-a6911c9c5ecd
-- title:
--   Tracks, branch-vertices and branches
-- statement:
--   A **track** is a nonnull connected graph, not a cycle, in which every vertex has degree at most $2$ (a path in the conventional sense); a track in a graph $H$ is a subgraph of $H$, not necessarily induced, which is a track. We list a track as its sequence $t_0, \dots, t_\ell$ of distinct vertices, consecutive ones adjacent in $H$; its **length** is $\ell$, its **ends** are $t_0, t_\ell$, its **internal vertices** are the others, and its edges are $t_{i}t_{i+1}$ ($0 \le i < \ell$).
--
--   A **branch-vertex** of $H$ is a vertex of degree at least $3$. A **branch** of $H$ is a maximal track $P$ in $H$ (under inclusion of subgraphs) such that no internal vertex of $P$ is a branch-vertex.
--
--   Tracks are needed because "path" in this paper always means induced path; tracks of $H$ correspond to paths of the line graph $L(H)$.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 74, §5, definitions of track, branch-vertex and branch

import Mathlib

namespace StrongPerfectGraph.LineGraph

/-- A **track** in `H` (p. 74): a subgraph of `H`, not necessarily induced, that is a nonnull
connected graph, not a cycle, with all degrees `≤ 2`; here listed as its sequence of distinct
vertices with consecutive entries adjacent in `H`. Its length is `p.length - 1`, its ends are the
first and last entries, its internal vertices the other entries (`p.tail.dropLast`). -/
def IsTrack {V : Type*} (H : SimpleGraph V) (p : List V) : Prop :=
  p ≠ [] ∧ p.Nodup ∧ p.IsChain H.Adj

/-- The edges of a track, in order along the track. -/
def trackEdgeList {V : Type*} (p : List V) : List (Sym2 V) :=
  (p.zip p.tail).map (fun x => s(x.1, x.2))

/-- The edge set of a track. -/
def trackEdges {V : Type*} (p : List V) : Set (Sym2 V) :=
  {e | e ∈ trackEdgeList p}

/-- A **branch-vertex** of `H` (p. 74): a vertex of degree at least three. -/
def IsBranchVertex {V : Type*} (H : SimpleGraph V) (v : V) : Prop :=
  ∃ s : Finset V, 3 ≤ s.card ∧ ∀ x ∈ s, H.Adj v x

/-- A **branch** of `H` (p. 74): a maximal track of `H` none of whose internal vertices is a
branch-vertex. Maximality is with respect to inclusion of subgraphs (vertices and edges). -/
def IsBranch {V : Type*} (H : SimpleGraph V) (p : List V) : Prop :=
  IsTrack H p ∧ (∀ z ∈ p.tail.dropLast, ¬ IsBranchVertex H z) ∧
    ∀ q : List V, IsTrack H q → (∀ z ∈ q.tail.dropLast, ¬ IsBranchVertex H z) →
      (∀ z ∈ p, z ∈ q) → trackEdges p ⊆ trackEdges q → ∀ z ∈ q, z ∈ p

end StrongPerfectGraph.LineGraph


