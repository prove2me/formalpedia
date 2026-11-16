-- Prove2me | Definitions.Def_DisjointPathsDAG_Supplement_PositiveCycles
-- name    : DisjointPathsDAG_Supplement_PositiveCycles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:00:19.335819+00:00
-- url     : https://prove2.me/theorems/3dcc6875-42f4-4cf9-afc9-608dcaef99c6
-- title:
--   Directed graphs whose cycles all have positive weight
-- statement:
--   Let $G$ be a directed multigraph with real edge weights $w$. $G$ has **only positive-weight cycles** if every closed directed walk of positive length has positive total weight; equivalently, every directed cycle has positive total weight, since a closed walk splits into directed cycles. A self-loop is a cycle of length one, so it must have positive weight; edges of negative weight are otherwise allowed.
--
--   Parallel edges are allowed. This is the hypothesis on the graph in Section 6 (Lemma 6.1 and Theorem 6.8).
--
--   **Formalization Note** Closed walks are lists of edges, as in `DisjointPathsDAG.Digraph.IsWalk`; the weight of a list is `DisjointPathsDAG.pathWeight`.
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Theorem 6.8, p.43, and Lemma 6.1, p.34

import Mathlib
import Definitions.Def_DisjointPathsDAG_Graph

set_option autoImplicit false

namespace DisjointPathsDAG.Supplement

/-!
# Directed graphs whose cycles all have positive weight

Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Theorem 6.8, p.43 ("Suppose every directed cycle
has positive total weight") and Lemma 6.1, p.34.

**Formalization Note** A hypothesis on a `DisjointPathsDAG.Digraph` with real weights (parallel edges
allowed). "Every directed cycle has positive total weight" is stated for every closed walk of positive
length; the two are equivalent, since a closed walk splits into directed cycles and a directed cycle is
a closed walk. A self-loop is a closed walk of length one, so it must have positive weight. Weights of
any sign are allowed otherwise.
-/

variable {n m : ℕ}

/-- Every closed walk of positive length (equivalently, every directed cycle) has positive weight. -/
def PositiveCycles (G : Digraph n m) (wt : Fin m → ℝ) : Prop :=
  ∀ (v : Fin n) (p : List (Fin m)), G.IsWalk Finset.univ v v p → p ≠ [] → 0 < pathWeight wt p

end DisjointPathsDAG.Supplement


