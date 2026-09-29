-- Prove2me | Definitions.Def_ShortestConnection_Principles_SpanningSubtree
-- name    : ShortestConnection_Principles_SpanningSubtree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:52:46.191529+00:00
-- url     : https://prove2.me/theorems/175033c4-b82b-4d8d-a801-2bdbe9c894b7
-- title:
--   Spanning subtrees, their length, shortest spanning subtrees (SSS) and the minimum length L
-- statement:
--   Let $V$ be a set of **terminals** and let $G$ be a simple graph on $V$ (a **labelled graph**: its edges are the possible links). Every unordered pair $\{a,b\}$ of terminals carries a real **length** $w(\{a,b\})$; only the lengths of edges of $G$ ever matter, and they may be negative or zero.
--
--   1. For a finite set $F$ of links, the **link graph** $H(F)$ is the graph on all of $V$ in which $a$ and $b$ are adjacent exactly when $\{a,b\} \in F$ and $a \ne b$.
--   2. $F$ is a **spanning subtree** of $G$ when every link of $F$ is an edge of $G$ and $H(F)$ is a tree on $V$ (connected, with no closed loops).
--   3. The **length** of $F$ is
--   $$\ell_w(F) = \sum_{e \in F} w(e).$$
--   4. $F$ is a **shortest spanning subtree (SSS)** of $G$ when it is a spanning subtree of $G$ and $\ell_w(F) \le \ell_w(F')$ for every spanning subtree $F'$ of $G$.
--   5. The **minimum length** $L(G,w)$ is the infimum of $\ell_w(F)$ over all spanning subtrees $F$ of $G$.
--
--   These are the objects of Prim's dictionary between connection networks and graphs: a connection network is a spanning subgraph without closed loops, and a shortest connection network (SCN) is a shortest spanning subtree (SSS). The complete graph with Euclidean distances is Prim's Basic Problem.
--
--   **Formalization Note** Lengths are a function $w : \mathrm{Sym}^2 V \to \mathbb{R}$ on unordered pairs. The minimum is taken over spanning subtrees only, never over connected spanning subgraphs; the two differ when lengths are negative. $L$ is a real infimum: for a connected finite $G$ it is the minimum of a finite nonempty set, and for a disconnected $G$ (no spanning subtree) it takes the junk value $0$, a case the mission never uses.
-- source:
--   Prim, Shortest Connection Networks And Some Generalizations, Bell System Tech. J. 36 (1957), p. 1389, Basic Problem; pp. 1395-1396, §IV (graph dictionary, SCN ↔ SSS); p. 1394, §III (the length L)

import Mathlib

namespace ShortestConnection.Principles

/-- The graph on all of `V` formed by a set `F` of links: two terminals are adjacent exactly when
the link joining them belongs to `F` (Prim 1957, §II: the links made so far; §IV: a spanning
subgraph of the labelled graph). -/
def linkGraph {V : Type*} (F : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (F : Set (Sym2 V))

/-- `F` is a spanning subtree of the labelled graph `G` (Prim 1957, pp. 1395–1396: "connection
network ↔ spanning subgraph (without closed loops) ↔ (spanning subtree)"): every link of `F` is an
edge of `G`, and the links of `F` form a tree on the whole vertex set `V`. -/
def IsSpanningSubtree {V : Type*} (G : SimpleGraph V) (F : Finset (Sym2 V)) : Prop :=
  (F : Set (Sym2 V)) ⊆ G.edgeSet ∧ (linkGraph F).IsTree

/-- The length of a set of links: the sum of the edge "lengths" `w e` over its links
(Prim 1957, p. 1389: "total length (sum of the link lengths)"). Lengths are arbitrary reals. -/
def length {V : Type*} (w : Sym2 V → ℝ) (F : Finset (Sym2 V)) : ℝ :=
  ∑ e ∈ F, w e

/-- `F` is a shortest spanning subtree (SSS) of `G` for the edge lengths `w`
(Prim 1957, p. 1396, "shortest connection network ↔ shortest spanning subtree, SCN ↔ SSS"):
`F` is a spanning subtree of `G` whose length is at most that of every spanning subtree of `G`.
The minimum is over spanning subtrees only, never over connected spanning subgraphs. -/
def IsSSS {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) (F : Finset (Sym2 V)) : Prop :=
  IsSpanningSubtree G F ∧ ∀ F' : Finset (Sym2 V), IsSpanningSubtree G F' → length w F ≤ length w F'

/-- The length `L` of a shortest spanning subtree of `G` (Prim 1957, p. 1394: "the length, L, of a
shortest connection network is simply the smallest length in this finite set of connection
network lengths"): the infimum of the lengths of all spanning subtrees of `G`. For a connected
finite `G` this set is finite and nonempty, so the infimum is attained; for a disconnected `G` the
set is empty and the value is the junk value `0`. -/
noncomputable def minLength {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) : ℝ :=
  sInf (length w '' {F : Finset (Sym2 V) | IsSpanningSubtree G F})

end ShortestConnection.Principles


