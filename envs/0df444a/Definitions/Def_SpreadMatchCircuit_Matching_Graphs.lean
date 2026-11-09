-- Prove2me | Definitions.Def_SpreadMatchCircuit_Matching_Graphs
-- name    : SpreadMatchCircuit_Matching_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:57.506033+00:00
-- url     : https://prove2.me/theorems/d9a0cdb8-3ea0-45eb-8f7b-c69b97570cfc
-- title:
--   Graphs on $[n]$, matchings, and the incident-edge graph $G(W)$
-- statement:
--   This file fixes the graph vocabulary of the mission. The vertex set is $[n]$, represented by `Fin n`. An **edge** is an unordered pair of distinct vertices, and a **graph** is a finite set of edges, so there are no loops or parallel edges.
--
--   1. For a set of edges $m$, $V(m)$ is the set of vertices incident to an edge of $m$.
--   2. A **matching** is a set of edges with pairwise disjoint endpoint sets. Its size $|m|$ is its number of edges.
--   3. A graph $x$ **has a matching of size $q$** if some matching with exactly $q$ edges is contained in $x$. The negation, "no matching of size $q$", says that the matching number of $x$ is less than $q$.
--   4. For a set of vertices $W$,
--   $$G(W)=\{e : e\cap W\neq\emptyset\}$$
--   is the graph of all edges with at least one endpoint in $W$. This is not the graph induced on $W$.
--   5. For $L\subseteq[n]$, an edge **crosses** $(L,L^{\mathrm c})$ if it has one endpoint in $L$ and one outside $L$; a graph is **bipartite with sides $L$ and $L^{\mathrm c}$** if all its edges cross.
--
--   These notions are used by every statement of the mission.
--
--   **Formalization Note** `Edge n` is the subtype of non-diagonal elements of `Sym2 (Fin n)`. A finite set of such edges corresponds exactly to a `SimpleGraph (Fin n)`. Edge sets are used instead of Mathlib's `Subgraph.IsMatching` so that matchings can be intersected, unioned and subtracted as the source does.
-- source:
--   Anup Rao, STOC 2027 submission #299 (October 2026), p. 4 (§1.2: matchings, G(W)), p. 8–9 (V(m)), p. 10 (bipartite universe)

import Mathlib

namespace SpreadMatchCircuit.Matching

open Finset

/-- An edge on the vertex set `Fin n`: an unordered pair of distinct vertices. A graph on `[n]`
is a `Finset (Edge n)`; there are no loops or parallel edges. -/
abbrev Edge (n : ℕ) : Type := {e : Sym2 (Fin n) // ¬ e.IsDiag}

variable {n : ℕ}

/-- The two endpoints of an edge. -/
def endpoints (e : Edge n) : Finset (Fin n) := e.1.toFinset

/-- `V(m)`: all vertices incident to an edge of `m`. -/
def verts (m : Finset (Edge n)) : Finset (Fin n) := m.biUnion endpoints

/-- A matching: a finite set of edges whose endpoint sets are pairwise disjoint. Its size is its
number of edges, `m.card`. -/
def IsMatching (m : Finset (Edge n)) : Prop :=
  ∀ e ∈ m, ∀ e' ∈ m, e ≠ e' → Disjoint (endpoints e) (endpoints e')

/-- The graph `x` has a matching of size `q`: some matching with exactly `q` edges is contained
in `x`. Its negation is "matching number `< q`". -/
def HasMatchingOfSize (x : Finset (Edge n)) (q : ℕ) : Prop :=
  ∃ m, m ⊆ x ∧ IsMatching m ∧ m.card = q

/-- `G(W)`: the graph containing exactly the edges with at least one endpoint in `W`
(not the graph induced on `W`). -/
def incident (W : Finset (Fin n)) : Finset (Edge n) :=
  univ.filter fun e => ¬ Disjoint (endpoints e) W

/-- `e` crosses the bipartition `(L, Lᶜ)`: exactly one endpoint lies in `L`. -/
def IsCrossEdge (L : Finset (Fin n)) (e : Edge n) : Prop :=
  ∃ u ∈ L, ∃ v, v ∉ L ∧ e.1 = s(u, v)

/-- The graph `x` is bipartite with sides `L` and `Lᶜ`. -/
def IsCrossGraph (L : Finset (Fin n)) (x : Finset (Edge n)) : Prop :=
  ∀ e ∈ x, IsCrossEdge L e

end SpreadMatchCircuit.Matching


