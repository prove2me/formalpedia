-- Prove2me | Definitions.Def_StochMatchPoly_mu
-- name    : StochMatchPoly_mu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:14:01.226852+00:00
-- url     : https://prove2.me/theorems/5d48310d-8f11-41fb-ac28-6d5d0ca00921
-- title:
--   Matchings, covered sets $V(M)$, the matching number $\mu$ and vertex degrees
-- statement:
--   Let $V$ be a finite vertex set. A graph on $V$ is identified with its set of edges, each edge an unordered pair of vertices; intersections of graphs on the common vertex set are intersections of edge sets.
--
--   1. A **matching** is a set $M$ of edges, none of them a loop, no two of which share a vertex.
--   2. $V(M)$ is the set of vertices **covered** by $M$, i.e. lying on some edge of $M$.
--   3. For an edge set $F$, $\mu(F)$ is the maximum cardinality of a matching $M\subseteq F$; the empty matching shows $\mu(F)\ge 0$.
--   4. For an edge set $H$ and a vertex $v$, $\deg_H(v)$ is the number of edges of $H$ containing $v$; the maximum degree satisfies $\Delta(H)\le R$ iff $\deg_H(v)\le R$ for every $v$.
--
--   These are the combinatorial objects of every statement of the mission: $\mu(G_p)$ and $\mu(H\cap G_p)$ in the goal, the covered sets $V(M)$ whose indicators appear in Lemma 3.1, and the degree bound $\Delta(H)\le R$.
--
--   **Formalization Note** Edges are elements of `Sym2 V`, edge sets are `Finset (Sym2 V)`, and $\mu$ is a maximum (`Finset.sup` of cardinalities) over the finite nonempty family of matchings contained in $F$, not a supremum of real numbers.
-- source:
--   S. Behnezhad, Stochastic Matching with Polynomial Degree, arXiv:2611.03367 (preprint, held version, sha256 409beb43bd8ab862a4a4a595be9c08afd92590790382102cb640d81d9b564017), §1 p.1 (PDF p.2); §4.1 Notation, p.9 (PDF p.10)

import Mathlib

open Classical

namespace StochMatchPoly

/-! # Matchings, covered sets and the matching number µ

S. Behnezhad, *Stochastic Matching with Polynomial Degree*, arXiv:2611.03367 (held version,
sha256 409beb43…), §1 p.1 and §4.1 "Notation", p.9 (PDF p.10).

"All graphs in the main argument are finite, undirected, and simple. … For a matching M, let V(M)
be its covered vertices. Write µ(K) for the maximum cardinality of a matching in K … Intersections
of graphs refer to their edge sets on the common vertex set."

**Formalization Note.** Vertices form a finite type `V`; an undirected edge is an element of
`Sym2 V`, and a graph on `V` is identified with its edge set, a `Finset (Sym2 V)` (for a
`SimpleGraph G` this is `G.edgeFinset`). Intersections of graphs on the common vertex set are then
intersections of edge sets. A matching is a set of non-loop edges, no two of which share a vertex.
`µ(F)` is the largest cardinality of a matching contained in `F`, a maximum over the finite,
nonempty family of such matchings (the empty matching gives `µ(F) ≥ 0`); it is a `Finset.sup` of
natural numbers, not a supremum of reals. -/

variable {V : Type*}

/-- A matching: no edge is a loop, and two edges of `M` that share a vertex are equal. -/
def IsMatchingSet (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, ¬ e.IsDiag) ∧ ∀ e ∈ M, ∀ f ∈ M, ∀ v : V, v ∈ e → v ∈ f → e = f

/-- `V(M)`: the vertices covered by the edge set `M`. -/
noncomputable def covered [Fintype V] (M : Finset (Sym2 V)) : Finset V :=
  Finset.univ.filter fun v => ∃ e ∈ M, v ∈ e

/-- `µ(F)`: the maximum cardinality of a matching contained in the edge set `F`. -/
noncomputable def mu (F : Finset (Sym2 V)) : ℕ :=
  (F.powerset.filter IsMatchingSet).sup Finset.card

/-- The degree of the vertex `v` in the graph with edge set `H`: the number of edges of `H`
containing `v`. `∆(H) ≤ R` is `∀ v, degIn H v ≤ R`. -/
noncomputable def degIn (H : Finset (Sym2 V)) (v : V) : ℕ :=
  (H.filter fun e => v ∈ e).card

end StochMatchPoly


