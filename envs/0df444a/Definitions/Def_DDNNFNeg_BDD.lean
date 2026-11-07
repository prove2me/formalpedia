-- Prove2me | Definitions.Def_DDNNFNeg_BDD
-- name    : DDNNFNeg_BDD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:12.565049+00:00
-- url     : https://prove2.me/theorems/11b3d03b-6c2f-47db-af11-fe13fd4f0bb1
-- title:
--   Nondeterministic branching program (DAG with a starting vertex)
-- statement:
--   A (nondeterministic) **branching program** over a set of variables $X$ is a directed acyclic graph with a distinguished starting vertex, whose vertices are sinks labelled $0$ or $1$, variable vertices and $\vee$ vertices (`BNode`). The **size** is the number of vertices.
--
--   **Formalization Note** Vertices are numbered $0, \dots, \mathrm{size}-1$ and every edge goes from a smaller to a larger index, which makes the graph acyclic. Several sinks with the same label are allowed (merging them only decreases the size); `BDD.HasUniqueSinks` imposes at most one sink of each label. Read-once, unambiguity, determinism and ordering are separate predicates.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Definition 3.2, p.9

import Mathlib
import Definitions.Def_DDNNFNeg_BNode

namespace DDNNFNeg

/-- A (nondeterministic) branching program over the variable set `X`
(Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), Definition 3.2, p.9): a DAG on the vertices `Fin size`, each vertex a sink, a variable
vertex or a `∨` vertex (`BNode`), with a distinguished starting vertex `start`. Every edge goes
from a smaller to a larger index, which makes the graph acyclic. The size is `size`, the
number of vertices.

**Formalization Note** The read-once ("free") condition, unambiguity, determinism and ordering
are separate predicates (`BDD.IsReadOnce`, `BDD.IsUnambiguous`, `BDD.IsDeterministic`,
`BDD.IsOrderedBy`). Several sinks with the same label are allowed by this structure; merging
them only decreases the size. `BDD.HasUniqueSinks` imposes at most one sink per label. -/
structure BDD (X : Type*) where
  /-- the number of vertices -/
  size : ℕ
  /-- the label of each vertex -/
  node : Fin size → BNode size X
  /-- the starting vertex -/
  start : Fin size
  /-- edges go from smaller to larger indices -/
  wf : ∀ k : Fin size, (∀ v lo hi, node k = .test v lo hi → k < lo ∧ k < hi) ∧
    (∀ l r, node k = .choice l r → k < l ∧ k < r)

end DDNNFNeg


