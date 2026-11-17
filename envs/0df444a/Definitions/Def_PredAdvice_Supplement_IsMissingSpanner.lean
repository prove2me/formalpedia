-- Prove2me | Definitions.Def_PredAdvice_Supplement_IsMissingSpanner
-- name    : PredAdvice_Supplement_IsMissingSpanner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:29:45.35808+00:00
-- url     : https://prove2.me/theorems/76f7903f-09ab-4ace-9d74-707a60c9048a
-- title:
--   Exact $r$-missing spanners of a directed graph
-- statement:
--   Let $G$ be a finite unweighted directed graph. An **exact $r$-missing spanner** of $G$ is a spanning subgraph $M\subseteq G$ (same vertex set, every edge of $M$ an edge of $G$) such that for every pair $(u,v)$ with $v$ reachable from $u$ there is a shortest $u$–$v$ path $P$ of $G$ with
--
--   $$|E(P)\setminus E(M)|\le r .$$
--
--   The size of $M$ is its number of edges, counted as ordered pairs.
--
--   This is the object bounded by Theorem 1.8 ($r=1$).
--
--   **Formalization Note** Shortest paths are the base mission's `PredAdvice.IsShortestPath` (vertex lists); the edges of a path are its consecutive pairs. A shortest path repeats no vertex, so counting consecutive pairs that are not edges of $M$ gives $|E(P)\setminus E(M)|$. Loops of $M$ are counted in its size.
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), exact r-missing spanners, §1.1, p.4; §6, p.25

import Mathlib
import Definitions.Def_PredAdvice_dist

set_option autoImplicit false

namespace PredAdvice

namespace Supplement

/-- An **exact `r`-missing spanner** of the directed graph `G` (Kopelowitz, Korin, Roditty,
*Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256
0ae8a68d…), §1.1, p.4; §6, p.25): "a spanning subgraph M ⊆ G such that, for every reachable pair
(u, v) in G, some shortest u–v path in G has at most r edges outside M."

**Formalization Note** `M` is a digraph on the same vertex set whose edges are edges of `G`. A
shortest path is the base mission's `PredAdvice.IsShortestPath` (a vertex list); its edges are its
consecutive pairs, and a shortest path repeats no vertex, so the number of consecutive pairs that
are not edges of `M` is `|E(P) ∖ E(M)|`. -/
def IsMissingSpanner {V : Type*} (G : Digraph V) (r : ℕ) (M : Digraph V) : Prop :=
  (∀ x y : V, M.Adj x y → G.Adj x y) ∧
    ∀ u v : V, Reachable G u v → ∃ p : List V, IsShortestPath G p u v ∧
      open Classical in ((p.zip p.tail).filter fun e => ¬ M.Adj e.1 e.2).length ≤ r

/-- The number of edges of a digraph `M`: the ordered pairs `(x, y)` with `M.Adj x y` (loops
included). -/
noncomputable def edgeCount {V : Type*} (M : Digraph V) : ℕ :=
  {e : V × V | M.Adj e.1 e.2}.ncard

end Supplement

end PredAdvice


