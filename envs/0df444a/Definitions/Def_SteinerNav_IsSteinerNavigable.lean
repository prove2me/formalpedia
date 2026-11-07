-- Prove2me | Definitions.Def_SteinerNav_IsSteinerNavigable
-- name    : SteinerNav_IsSteinerNavigable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:46:47.615111+00:00
-- url     : https://prove2.me/theorems/a4b6911d-1674-496b-a67d-dcaa2485ab56
-- title:
--   $\alpha$-navigable graph with Steiner points (Definition 1); no Steiner-to-Steiner edges
-- statement:
--   Let $\alpha>1$ and let $P\subset\mathbb R^d$ be a finite set of input points.
--
--   1. **Definition 1.** An **$\alpha$-navigable graph with Steiner points** for $P$ is a directed graph $G=(P\cup R,E)$, for some finite set $R\subset\mathbb R^d\setminus P$ of **Steiner points**, such that for every vertex $s\in P\cup R$ the out-neighbors of $s$ $\alpha$-cover $P$ with respect to $s$: for every $t\in P\setminus\{s\}$ there is an edge $(s,v)\in E$ with $\|v-t\|<\|s-t\|/\alpha$. When $R=\emptyset$ this is an $\alpha$-navigable graph.
--   2. $G$ has **no Steiner-to-Steiner edges** if every edge leaving a vertex of $R$ ends in $P$.
--
--   Sources range over all vertices, Steiner points included, but targets range over the input points only: Steiner points need not be reachable.
--
--   **Formalization Note** The graph is a finite set $E$ of ordered pairs of points, each with both ends in $P\cup R$; $R$ is a finite set disjoint from $P$. Definition 1 does not exclude self-loops or Steiner-to-Steiner edges, and neither does the definition here; the second property is a separate predicate.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee6…), Definition 1, pp.5–6; "no Steiner-to-Steiner edges", Theorem 3, p.8

import Mathlib
import Definitions.Def_SteinerNav_Covers

namespace SteinerNav

/-- Definition 1: `G = (P ∪ R, E)` is an `α`-navigable graph with Steiner points for `P`: `R` is a
finite set of points outside `P`, every edge has both ends in `P ∪ R`, and for every `s ∈ P ∪ R` the
out-neighbors of `s` `α`-cover `P` with respect to `s` (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), Definition 1, pp.5–6).

**Formalization Note** The directed graph is a `Finset` of ordered pairs of points. Sources range
over `P ∪ R`, targets over `P` only. Self-loops and Steiner-to-Steiner edges are allowed here, as in
Definition 1. -/
def IsSteinerNavigable {d : ℕ} (α : ℝ) (P R : Finset (Pt d)) (E : Finset (Pt d × Pt d)) : Prop :=
  Disjoint R P ∧
    (∀ x y, (x, y) ∈ E → x ∈ P ∪ R ∧ y ∈ P ∪ R) ∧
    ∀ s ∈ P ∪ R, ∀ t ∈ P, t ≠ s → ∃ v, (s, v) ∈ E ∧ Covers α s v t

/-- `G` has no Steiner-to-Steiner edges: every edge leaving a vertex of `R` ends in `P`
(Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), Theorem 3, p.8). -/
def NoSteinerToSteiner {d : ℕ} (R P : Finset (Pt d)) (E : Finset (Pt d × Pt d)) : Prop :=
  ∀ x y, (x, y) ∈ E → x ∈ R → y ∈ P

end SteinerNav


