-- Prove2me | Definitions.Def_TenChallenges_TopologicalMinor
-- name    : TenChallenges_TopologicalMinor
-- status  : Definition
-- author  : @Davide
-- created : 2026-11-18T12:39:16.648694+00:00
-- url     : https://prove2.me/theorems/88095b94-f065-4efa-9b53-f749ab58e1ff
-- title:
--   Topological minor (subdivision) of a simple graph
-- statement:
--   A graph $G$ contains a **subdivision** of a graph $H$ (equivalently, $H$ is a **topological minor** of $G$) if there are
--
--   - an injective map $v\mapsto \varphi(v)$ from the vertices of $H$ to vertices of $G$ (the *branch vertices*), and
--   - for every edge $ab$ of $H$ a path $P_{ab}$ in $G$ from $\varphi(a)$ to $\varphi(b)$,
--
--   such that no path $P_{ab}$ passes through a branch vertex other than $\varphi(a)$ and $\varphi(b)$, and paths belonging to distinct edges of $H$ meet only in branch vertices. Equivalently, $G$ has a subgraph obtained from $H$ by replacing its edges with internally disjoint paths. This is the containment relation of Kuratowski's theorem.
--
--   **Formalization Note** The structure stores a path for each ordered adjacency `H.Adj a b`; the paths for `(a,b)` and `(b,a)` are not required to agree, since they belong to the same edge $s(a,b)$ and the disjointness condition is only imposed for distinct edges. Any such data yields a subdivision by keeping one path per edge.
-- source:
--   Standard notion; Kuratowski, Sur le problème des courbes gauches en topologie, Fund. Math. 15 (1930), 271–283 ('subgraph homeomorphic to K_5 or K_{3,3}'); see e.g. Diestel, Graph Theory, Sect. 1.7 (topological minors).

import Mathlib.Combinatorics.SimpleGraph.Paths

namespace SimpleGraph

variable {W V : Type*}

/-- The data witnessing that `G` contains a subdivision of `H` (a *topological minor*):
an injective map sending the vertices of `H` to *branch vertices* of `G`, and for every edge
`ab` of `H` a path of `G` from the branch vertex of `a` to that of `b`, such that a path meets
no branch vertex other than its two ends, and paths of distinct edges of `H` share only
branch vertices. -/
structure TopologicalMinor (H : SimpleGraph W) (G : SimpleGraph V) where
  /-- The branch vertex of each vertex of `H`. -/
  vertexMap : W ↪ V
  /-- The subdivided edge: a path between the branch vertices of the ends. -/
  path : ∀ ⦃a b : W⦄, H.Adj a b → G.Walk (vertexMap a) (vertexMap b)
  /-- Each subdivided edge is a path. -/
  path_isPath : ∀ ⦃a b : W⦄ (h : H.Adj a b), (path h).IsPath
  /-- A subdivided edge meets no branch vertex except its two ends. -/
  path_branch : ∀ ⦃a b : W⦄ (h : H.Adj a b) (x : W),
    vertexMap x ∈ (path h).support → x = a ∨ x = b
  /-- Subdivided edges of distinct edges of `H` meet only in branch vertices. -/
  path_disjoint : ∀ ⦃a b c d : W⦄ (h : H.Adj a b) (k : H.Adj c d), s(a, b) ≠ s(c, d) →
    ∀ v, v ∈ (path h).support → v ∈ (path k).support → ∃ x, vertexMap x = v

end SimpleGraph


