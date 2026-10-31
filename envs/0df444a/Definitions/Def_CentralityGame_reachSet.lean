-- Prove2me | Definitions.Def_CentralityGame_reachSet
-- name    : CentralityGame_reachSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:25.328346+00:00
-- url     : https://prove2.me/theorems/ade4d68a-ba55-4820-b870-bb3f8f961078
-- title:
--   The set $\mathcal N_i^{-\infty}$ of nodes that reach $i$
-- statement:
--   $\mathcal N_i^{-\infty}$ is the set of all nodes from which $i$ is reachable:
--
--   $$
--   \mathcal N_i^{-\infty}=\bigcup_{l\ge 0}\mathcal N_i^{-l}.
--   $$
--
--   It contains $i$, so $|\mathcal N_i^{-\infty}|>d_i$ means that at least $d_i$ other nodes reach $i$. This cardinality separates the two cases of Theorem 1.
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, §2, p.5

import Mathlib
import Definitions.Def_CentralityGame_reachWithin

namespace CentralityGame

/-- The set `N_i^{-∞} = ⋃_{l ≥ 0} N_i^{-l}` (Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, §2, p.5): all nodes from which
`i` is reachable. It contains `i`. -/
noncomputable def reachSet {V : Type*} [Fintype V] (N : V → Finset V) (i : V) : Finset V :=
  (Set.toFinite {j | ∃ l, j ∈ reachWithin N i l}).toFinset

end CentralityGame


