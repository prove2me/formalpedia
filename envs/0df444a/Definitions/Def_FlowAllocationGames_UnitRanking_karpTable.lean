-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_karpTable
-- name    : FlowAllocationGames_UnitRanking_karpTable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:27:45.89461+00:00
-- url     : https://prove2.me/theorems/8943c0d8-b564-4d07-84fe-de4cfb8eb37d
-- title:
--   Karp's walk table
-- statement:
--   Computes the layers $D_0, \dots, D_N$ of Karp's minimum-mean-cycle algorithm, where $N$ is the number of nodes, $D_0 \equiv 0$ (walks may start anywhere), and $D_k(v)$ is the minimum cost of a walk with exactly $k$ arcs ending at $v$, with the last arc of such a walk.
--
--   This is part of the witness algorithm of the mission: the paper computes the optimal circulation $f^*$ by citing Tardos [45] and fixes no algorithm.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 23; Karp, Discrete Math. 23 (1978)

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Cost
import Definitions.Def_FlowAllocationGames_UnitRanking_tick
import Definitions.Def_FlowAllocationGames_UnitRanking_ResArc
import Definitions.Def_FlowAllocationGames_UnitRanking_karpLayer

namespace FlowAllocationGames.UnitRanking

/-- **Karp's walk table.**
Witness algorithm of the mission for "f∗ can be computed in strongly polynomial time [45]" in
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 23. Karp, Discrete Math. 23 (1978).

Returns the layers `k = 0, …, N`: layer `k` holds `D_k[v]`, the minimum cost of a walk with exactly
`k` arcs ending at `v` (from any start node; `D_0 = 0`), and the last arc of such a walk. -/
def karpTable (N : ℕ) (arcs : List ResArc) :
    StateM Cost (Array (Array (Option ℤ) × Array (Option ResArc))) := do
  let mut D : Array (Option ℤ) := Array.replicate N (some 0)
  let mut layers : Array (Array (Option ℤ) × Array (Option ResArc)) :=
    #[(D, Array.replicate N none)]
  for _ in List.range N do
    tick 1
    let (D', P') ← karpLayer N arcs D
    layers := layers.push (D', P')
    D := D'
  pure layers

end FlowAllocationGames.UnitRanking


