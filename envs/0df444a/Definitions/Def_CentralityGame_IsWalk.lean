-- Prove2me | Definitions.Def_CentralityGame_IsWalk
-- name    : CentralityGame_IsWalk
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:11:44.508409+00:00
-- url     : https://prove2.me/theorems/583f748e-8c2c-4f93-8bf8-33b4f2b87771
-- title:
--   Length-$l$ walk
-- statement:
--   A **length-$l$ walk** in a graph is an $(l+1)$-tuple of nodes $(r_0,r_1,\dots,r_l)$ such that $(r_{h-1},r_h)\in\mathcal E$ for every $1\le h\le l$. It is a walk from $r_0$ to $r_l$; for $l=0$ a single node is a walk.
--
--   Walks define the incoming neighbourhoods $\mathcal N_i^{-l}$ and paths.
--
--   **Formalization Note** The tuple is a function on $\{0,\dots,l\}$; the endpoints are read off as its first and last values.
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, §2, p.5

import Mathlib

namespace CentralityGame

/-- A **length-`l` walk** in the graph with out-neighbourhoods `N` (Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, §2,
p.5): an `(l + 1)`-tuple of nodes `(r_0, …, r_l)` with `(r_{h-1}, r_h) ∈ E` for every
`1 ≤ h ≤ l`. It is a walk from `r 0` to `r (Fin.last l)`.

**Formalization Note** The tuple is `r : Fin (l + 1) → V`. The endpoints are not parameters; the
statements that use a walk from `i` to `j` add `r 0 = i` and `r (Fin.last l) = j`. -/
def IsWalk {V : Type*} (N : V → Finset V) {l : ℕ} (r : Fin (l + 1) → V) : Prop :=
  ∀ h : Fin l, r h.succ ∈ N (r h.castSucc)

end CentralityGame


