-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_minMeanCycle
-- name    : FlowAllocationGames_UnitRanking_minMeanCycle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:28:33.638302+00:00
-- url     : https://prove2.me/theorems/76c167a1-6ad6-4e90-9997-353d43caac9a
-- title:
--   A negative residual cycle of minimum mean cost
-- statement:
--   Computes Karp's minimum cycle mean of the residual network of $x$,
--
--   $$
--   \mu = \min_{v} \max_{k < N} \frac{D_N(v) - D_k(v)}{N - k},
--   $$
--
--   over the nodes with $D_N(v)$ finite and the $k$ with $D_k(v)$ finite, comparing fractions by cross-multiplication (ties to the lowest index). If no node qualifies or $\mu \ge 0$ there is no negative cycle and the result is "none". Otherwise it walks back along the $N$-arc walk to the minimizing node and returns the first cycle closed on that walk, which has mean cost $\mu$.
--
--   This is part of the witness algorithm of the mission: the paper computes the optimal circulation $f^*$ by citing Tardos [45] and fixes no algorithm.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 23; Karp, Discrete Math. 23 (1978)

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Cost
import Definitions.Def_FlowAllocationGames_UnitRanking_tick
import Definitions.Def_FlowAllocationGames_UnitRanking_zsub
import Definitions.Def_FlowAllocationGames_UnitRanking_zmul
import Definitions.Def_FlowAllocationGames_UnitRanking_zlt
import Definitions.Def_FlowAllocationGames_UnitRanking_Net
import Definitions.Def_FlowAllocationGames_UnitRanking_ResArc
import Definitions.Def_FlowAllocationGames_UnitRanking_residualArcs
import Definitions.Def_FlowAllocationGames_UnitRanking_karpTable

namespace FlowAllocationGames.UnitRanking

/-- **A negative cycle of minimum mean cost in the residual network.**
Witness algorithm of the mission for "f∗ can be computed in strongly polynomial time [45]" in
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 23. Karp, Discrete Math. 23 (1978).

Builds the residual network of `x` and Karp's table `D_0, …, D_N` (`N` the number of nodes). The
minimum cycle mean is `μ = min_v max_{k < N} (D_N[v] − D_k[v]) / (N − k)`, over the `v` with
`D_N[v]` finite and the `k` with `D_k[v]` finite; fractions are compared by cross-multiplication in
`ℤ`, and ties go to the lowest index. If there is no such `v` or `μ ≥ 0`, returns `none`.
Otherwise it follows the last arcs of the `N`-arc walk to the minimizing `v` backwards and returns
the first cycle closed on that walk, as its list of arcs in forward order. -/
def minMeanCycle (G : Net) (x : Array ℤ) : StateM Cost (Option (List ResArc)) := do
  let N := G.N
  let arcs ← residualArcs G x
  let layers ← karpTable N arcs
  let DN := (layers.getD N default).1
  let mut best : Option (ℤ × ℤ × ℕ) := none
  for v in List.range N do
    tick 1
    match DN.getD v none with
    | none => pure ()
    | some dN =>
      let mut worst : Option (ℤ × ℤ) := none
      for k in List.range N do
        tick 1
        match (layers.getD k default).1.getD v none with
        | none => pure ()
        | some dk =>
          let num ← zsub dN dk
          let den : ℤ := ((N - k : ℕ) : ℤ)
          match worst with
          | none => worst := some (num, den)
          | some (p, q) =>
            let l ← zmul p den
            let r ← zmul num q
            if ← zlt l r then
              worst := some (num, den)
      match worst with
      | none => pure ()
      | some (p, q) =>
        match best with
        | none => best := some (p, q, v)
        | some (p', q', _) =>
          let l ← zmul p q'
          let r ← zmul p' q
          if ← zlt l r then
            best := some (p, q, v)
  match best with
  | none => pure none
  | some (p, _, v) =>
    if !(← zlt p 0) then
      pure none
    else
      let mut cur : ℕ := v
      let mut visited : List ℕ := [v]
      let mut walk : List ResArc := []
      let mut cycle : Option (List ResArc) := none
      for i in List.range N do
        tick 1
        if cycle.isNone then
          match (layers.getD (N - i) default).2.getD cur none with
          | none => pure ()
          | some a =>
            walk := a :: walk
            for _ in visited do
              tick 1
            let idx := visited.idxOf a.src
            if idx < visited.length then
              cycle := some (walk.take (idx + 1))
            else
              visited := a.src :: visited
              cur := a.src
      pure cycle

end FlowAllocationGames.UnitRanking


