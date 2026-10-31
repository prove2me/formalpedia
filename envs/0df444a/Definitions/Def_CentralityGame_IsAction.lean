-- Prove2me | Definitions.Def_CentralityGame_IsAction
-- name    : CentralityGame_IsAction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:11:48.87741+00:00
-- url     : https://prove2.me/theorems/043efc97-eec4-4d1e-bfa3-2542d1d6e42c
-- title:
--   Action set $\mathcal A_i$
-- statement:
--   The **action set** $\mathcal A_i$ of a player $i$ is the family of all $\binom{n-1}{d_i}$ subsets of $\mathcal V\setminus\{i\}$ of cardinality $d_i$: a set $a$ is an action of $i$ when $i\notin a$ and $|a|=d_i$.
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, §3, p.8

import Mathlib

namespace CentralityGame

/-- The action set `A_i` of player `i` (Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, §3, p.8): the subsets of `V ∖ {i}`
of cardinality `d_i`. -/
def IsAction {V : Type*} (d : V → ℕ) (i : V) (a : Finset V) : Prop :=
  i ∉ a ∧ a.card = d i

end CentralityGame


