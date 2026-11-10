-- Prove2me | Definitions.Def_LoadBalMatch_Main_Matching
-- name    : LoadBalMatch_Main_Matching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:31:43.788794+00:00
-- url     : https://prove2.me/theorems/7a93e629-acb6-4f98-948f-03613b26dcbc
-- title:
--   Matchings, the matching number $\mu$, maximal matchings, edge streams and $H\cup F$ (§2)
-- statement:
--   Let $V$ be a finite vertex set and let graphs on $V$ be simple (no loops, no parallel edges); an edge is an unordered pair $\{u,v\}$ with $u\neq v$. A **matching** of a graph $H$ is a set $M$ of edges of $H$, no two of which share a vertex. The **matching number** is
--   $$\mu(H)=\max\{|M| : M \text{ a matching of } H\},$$
--   and $M$ is a **maximum matching** if it is a matching with $|M|=\mu(H)$. A matching $M$ of $G$ is **maximal** if every edge of $G$ shares a vertex with some edge of $M$. A vertex $v$ is **covered** by $M$ if some edge of $M$ contains it. For a graph $H$ and a set $F$ of pairs, $H\cup F$ is the graph on $V$ whose edges are those of $H$ together with the non-loop pairs of $F$; a subgraph $H\subseteq G$ keeps the vertex set $V$ and takes a subset of the edges. An **edge stream** of $G$ is a list of the edges of $G$ in which every edge of $G$ occurs exactly once, in an arbitrary order.
--
--   These are the basic objects of the whole paper: the algorithm's goal is a matching whose size is close to $\mu(G)$, read from an edge stream.
--
--   **Formalization Note.** `IsMatchingIn H M` for `M : Finset (Sym2 V)`; `matchingNumber H` is the largest cardinality of such an `M` (a maximum over a finite set); `addEdges H F = H ⊔ fromEdgeSet F`; `IsEdgeStream G σ` says `σ` is duplicate-free and its entries are exactly the edges of `G`.
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 1, §1; p. 3, §2 (Notation)

import Mathlib

/-!
# Matchings, the matching number µ, edge streams and adding edges to a graph

Assadi, Bernstein, Wrzos-Kaminska, *Better Bounds for Semi-Streaming Maximum Matching via Load
Balancing*, STOC 2027 submission (sha256 7cd28a8b…), §1 p. 1, §2 p. 3: "Given a graph G = (V, E),
let n = |V|. We use µ(G) to denote the size of the maximum matching in G."

Conventions. Vertices form a finite type `V`; a graph is a `SimpleGraph V` (no loops, no parallel
edges); an edge is an unordered pair `Sym2 V`. A subgraph `H ⊆ G` keeps the vertex set `V`
(`H ≤ G`). `addEdges H F` is the graph `H ∪ F` obtained by adding the (non-loop) pairs in `F`.
An edge stream of `G` lists every edge of `G` exactly once, in an arbitrary order.
-/

namespace LoadBalMatch.Main

variable {V : Type*}

/-- `M` is a matching of `H`: every element of `M` is an edge of `H`, and two distinct elements
of `M` share no vertex. -/
def IsMatchingIn (H : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ H.edgeSet) ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v, v ∈ e → v ∉ f

/-- `µ(H)`: the largest cardinality of a matching of `H`. -/
noncomputable def matchingNumber [Fintype V] [DecidableEq V] (H : SimpleGraph V) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset (Sym2 V))).filter (IsMatchingIn H)).sup Finset.card

/-- `M` is a maximum matching of `H`. -/
def IsMaximumMatching [Fintype V] [DecidableEq V] (H : SimpleGraph V) (M : Finset (Sym2 V)) :
    Prop :=
  IsMatchingIn H M ∧ M.card = matchingNumber H

/-- `M` is a maximal matching of `G`: a matching of `G` that shares a vertex with every edge
of `G`. -/
def IsMaximalMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  IsMatchingIn G M ∧ ∀ e ∈ G.edgeSet, ∃ f ∈ M, ∃ v, v ∈ e ∧ v ∈ f

/-- The vertex `v` is covered by (an edge of) `M`. -/
def Covers (M : Finset (Sym2 V)) (v : V) : Prop :=
  ∃ e ∈ M, v ∈ e

/-- The graph `H ∪ F`: `H` with the non-loop pairs of `F` added as edges. -/
def addEdges (H : SimpleGraph V) (F : Set (Sym2 V)) : SimpleGraph V :=
  H ⊔ SimpleGraph.fromEdgeSet F

/-- `σ` is an edge stream of `G`: it lists every edge of `G` exactly once, in any order. -/
def IsEdgeStream (G : SimpleGraph V) (σ : List (Sym2 V)) : Prop :=
  σ.Nodup ∧ ∀ e, e ∈ σ ↔ e ∈ G.edgeSet

end LoadBalMatch.Main


