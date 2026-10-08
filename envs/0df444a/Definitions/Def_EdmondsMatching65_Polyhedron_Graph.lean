-- Prove2me | Definitions.Def_EdmondsMatching65_Polyhedron_Graph
-- name    : EdmondsMatching65_Polyhedron_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T14:05:46.729773+00:00
-- url     : https://prove2.me/theorems/58a7c3c3-4ebe-4a46-9c78-345da2c9111c
-- title:
--   Finite graphs with parallel edges, matchings, incidence vectors and maximum-weight matchings
-- statement:
--   Let $G$ be a finite graph with node set $V$ and edge set $E$: each edge $e$ meets an unordered pair $\{v_1,v_2\}$ of two **different** nodes, its ends. Several edges may have the same pair of ends (parallel edges), but no edge is a loop.
--
--   1. A **matching** in $G$ is a set $M\subseteq E$ of edges no two of which meet the same node.
--   2. The **incidence vector** of a set of edges $M$ is the 0–1 vector $\chi^M\in\mathbb R^E$ with $\chi^M_e=1$ if $e\in M$ and $\chi^M_e=0$ otherwise.
--   3. Given real edge weights $c\in\mathbb R^E$ (of any sign), a matching $M$ is **maximum** if its weight-sum is at least that of every matching:
--   $$\sum_{e\in M'}c_e\;\le\;\sum_{e\in M}c_e\qquad\text{for every matching }M'.$$
--
--   These are the basic objects of Edmonds' paper: the maximum-weight-sum matching problem asks for a matching of largest total weight.
--
--   **Formalization Note** The graph is given by a finite node type $V$, a finite edge type $E$ and, for each edge, the unordered pair of its ends (no loops). Parallel edges are allowed, which covers the contracted graphs of Theorem (M); a simple graph is the special case of an injective end map. Vectors $x$ have one real coordinate per edge.
-- source:
--   Edmonds, Maximum Matching and a Polyhedron With 0,1-Vertices, J. Res. NBS 69B (1965), p. 125, §1 (graph, matching, maximum-weight-sum matching); p. 126, §2 (vectors < x > as edge subsets)

import Mathlib

namespace EdmondsMatching65.Polyhedron

/-- A finite graph in the sense of Edmonds (1965), §1–§2, pp. 125–126: nodes `V`, edges `E`, and for
each edge the unordered pair of nodes it meets. Parallel edges are allowed (the contracted graphs
`Gᵢ` of Theorem (M) have them); loops are excluded. Finiteness is supplied by `[Fintype V]
[Fintype E]` at every use. A simple graph is the case `Function.Injective G.ends`. -/
structure Graph (V E : Type*) where
  /-- the unordered pair of end nodes of an edge -/
  ends : E → Sym2 V
  /-- no edge is a loop: its two ends are different nodes -/
  loopless : ∀ e, ¬ (ends e).IsDiag

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- A *matching* in `G` (§1, p. 125): a set of edges no two of which meet the same node. -/
def IsMatching (G : Graph V E) (M : Finset E) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v : V, v ∈ G.ends e → v ∉ G.ends f

/-- The incidence (0–1) vector of a set of edges `M`: `x e = 1` exactly when `e ∈ M`. -/
def incidence (M : Finset E) : E → ℝ :=
  fun e => if e ∈ M then 1 else 0

/-- A *maximum* matching for real edge weights `c` (§1, p. 125: a maximum-weight-sum matching):
a matching whose weight-sum `∑_{e ∈ M} c e` is at least that of every matching of `G`. -/
def IsMaximumMatching (G : Graph V E) (c : E → ℝ) (M : Finset E) : Prop :=
  IsMatching G M ∧ ∀ M' : Finset E, IsMatching G M' → ∑ e ∈ M', c e ≤ ∑ e ∈ M, c e

end EdmondsMatching65.Polyhedron


