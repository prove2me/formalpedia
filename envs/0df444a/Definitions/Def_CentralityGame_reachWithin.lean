-- Prove2me | Definitions.Def_CentralityGame_reachWithin
-- name    : CentralityGame_reachWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:22.324006+00:00
-- url     : https://prove2.me/theorems/11073a6d-20c8-4a6e-9c58-ab19bcc6a73a
-- title:
--   Incoming neighbourhood $\mathcal N_i^{-l}$
-- statement:
--   For a node $i$ and an integer $l\ge 0$, $\mathcal N_i^{-l}$ is the set of nodes $j$ for which there exists a walk of length at most $l$ from $j$ to $i$. The node $i$ belongs to it for every $l$, through the walk of length $0$.
--
--   These sets measure incoming distance: Theorem 1 states that a best response links only inside $\mathcal N_i^{-d_i}$.
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, §2, p.5

import Mathlib
import Definitions.Def_CentralityGame_IsWalk

namespace CentralityGame

/-- The set `N_i^{-l}` (Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, §2, p.5): the nodes `j` for which there exists a
walk of length at most `l` from `j` to `i`.

**Formalization Note** `i` itself belongs to `N_i^{-l}` for every `l` (the length-0 walk), and
walks may pass through `i`, as on the page. -/
noncomputable def reachWithin {V : Type*} [Fintype V] (N : V → Finset V) (i : V) (l : ℕ) :
    Finset V :=
  (Set.toFinite {j | ∃ m, m ≤ l ∧ ∃ r : Fin (m + 1) → V, IsWalk N r ∧ r 0 = j ∧
    r (Fin.last m) = i}).toFinset

end CentralityGame


