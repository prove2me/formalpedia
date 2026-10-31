-- Prove2me | Definitions.Def_CentralityGame_IsOutDegreeProfile
-- name    : CentralityGame_IsOutDegreeProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:11:45.882552+00:00
-- url     : https://prove2.me/theorems/db315b30-82a0-4018-804e-8b3b1c5782ae
-- title:
--   Out-degree profile $\mathbf d\in\{1,\dots,n-1\}^{\mathcal V}$
-- statement:
--   An **out-degree profile** of a centrality game on $n=|\mathcal V|$ nodes is an integer vector $\mathbf d$ in $\{1,\dots,n-1\}^{\mathcal V}$. Each node $i$ must place exactly $d_i$ out-links, and the bounds guarantee that this is possible.
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, §3, p.8

import Mathlib

namespace CentralityGame

/-- An out-degree profile of a centrality game (Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, §3, p.8): an integer vector
`d` in `{1, …, n - 1}^V`, where `n = |V|`. -/
def IsOutDegreeProfile {V : Type*} [Fintype V] (d : V → ℕ) : Prop :=
  ∀ i, 1 ≤ d i ∧ d i ≤ Fintype.card V - 1

end CentralityGame


