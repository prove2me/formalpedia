-- Prove2me | Definitions.Def_AppliedComb_GraphAlg_SpanningTree
-- name    : AppliedComb_GraphAlg_SpanningTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:32:13.719111+00:00
-- url     : https://prove2.me/theorems/018d6862-74ed-47c9-a1de-29c30cf312f8
-- title:
--   Spanning forests, spanning trees and their weight (Section 12.1)
-- statement:
--   Let $G = (V, E)$ be a finite graph.
--
--   - A **spanning forest** of $G$ is a graph $H = (V, S)$ on the same vertex set with $S \subseteq E$ that is acyclic (contains no cycle).
--   - A **spanning tree** of $G$ is a graph $T = (V, S)$ with $S \subseteq E$ that is a tree, i.e. connected and acyclic.
--   - Given a **weight** $w(e) \in \mathbb{N}_0$ for every edge $e$, the weight of a set $S$ of edges is
--   $$w(S) = \sum_{e \in S} w(e),$$
--   and the weight of a subgraph $H = (V, S)$, in particular of a spanning tree, is $w(S)$.
--
--   These are the objects of the minimum weight spanning tree problem (Problem 12.2): find a spanning tree of a connected weighted graph whose weight is as small as possible.
--
--   **Formalization Note.** Graphs are Mathlib's `SimpleGraph V`; a subgraph on the full vertex set is another `SimpleGraph V` with `H ≤ G`. Acyclic and tree are Mathlib's `SimpleGraph.IsAcyclic` and `SimpleGraph.IsTree` (connected, which includes a nonempty vertex set, and acyclic). The weight is a function `w : Sym2 V → ℕ` on unordered pairs; only its values on edges of the graph are used, so it plays the role of the book's $w : E \to \mathbb{N}_0$. `weight w H` sums `w` over the finite edge set of `H` (the vertex type is a `Fintype`).
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), pp. 239–241, Section 12.1 (weight, spanning forest, spanning tree)

import Mathlib

namespace AppliedComb.GraphAlg

/-- Keller–Trotter, p. 240. A *spanning forest* `H = (V, S)` of a graph `G = (V, E)` is an
acyclic subgraph of `G` on the whole vertex set `V`. A `SimpleGraph V` on the same vertex type
automatically has vertex set `V`; `H ≤ G` says `S ⊆ E`, and acyclicity is Mathlib's
`SimpleGraph.IsAcyclic` (no cycle). -/
def IsSpanningForest {V : Type*} (G H : SimpleGraph V) : Prop :=
  H ≤ G ∧ H.IsAcyclic

/-- Keller–Trotter, pp. 240–241. A *spanning tree* `T = (V, S)` of a graph `G` is a subgraph of
`G` on the whole vertex set `V` that is a tree (connected and acyclic, Mathlib's
`SimpleGraph.IsTree`). -/
def IsSpanningTree {V : Type*} (G T : SimpleGraph V) : Prop :=
  T ≤ G ∧ T.IsTree

open Classical in
/-- Keller–Trotter, p. 239. Given a weight `w(e) ∈ ℕ₀` on the edges, the *weight* of a set `S`
of edges is `w(S) = ∑_{e ∈ S} w(e)`; the weight of a subgraph `H = (V, S)` (in particular of a
spanning tree) is the weight of its edge set. The weight is a function `Sym2 V → ℕ`; only its
values on edges of the graph under consideration are ever used. -/
noncomputable def weight {V : Type*} [Fintype V] (w : Sym2 V → ℕ) (H : SimpleGraph V) : ℕ :=
  ∑ e ∈ H.edgeFinset, w e

end AppliedComb.GraphAlg


