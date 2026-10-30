-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_karpLayer
-- name    : FlowAllocationGames_UnitRanking_karpLayer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:27:13.682329+00:00
-- url     : https://prove2.me/theorems/94ec33c5-12fc-487c-9a28-16790cc6cd63
-- title:
--   One layer of Karp's walk table
-- statement:
--   Given, for every node $v$, the minimum cost $D_k(v)$ of a walk with exactly $k$ arcs ending at $v$ (or "none"), computes
--
--   $$
--   D_{k+1}(v) = \min_{u \to v} \bigl(D_k(u) + \mathrm{cost}(u \to v)\bigr)
--   $$
--
--   over the residual arcs entering $v$, together with a minimizing last arc (the first one found). All additions and comparisons are ticked.
--
--   This is part of the witness algorithm of the mission: the paper computes the optimal circulation $f^*$ by citing Tardos [45] and fixes no algorithm.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 23; Karp, Discrete Math. 23 (1978)

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Cost
import Definitions.Def_FlowAllocationGames_UnitRanking_tick
import Definitions.Def_FlowAllocationGames_UnitRanking_zadd
import Definitions.Def_FlowAllocationGames_UnitRanking_zlt
import Definitions.Def_FlowAllocationGames_UnitRanking_ResArc

namespace FlowAllocationGames.UnitRanking

/-- **One layer of Karp's walk table.**
Witness algorithm of the mission for "f∗ can be computed in strongly polynomial time [45]" in
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 23. Karp, *A characterization of the minimum cycle mean in a digraph*, Discrete Math. 23 (1978).

Given `D[v]`, the minimum cost of a walk with exactly `k` arcs ending at `v` (`none` if there is no
such walk), returns the same table for `k + 1` arcs, `D'[v] = min over arcs u → v of D[u] + cost`,
together with a minimizing last arc for each `v` (the first one found, in the order of `arcs`). -/
def karpLayer (N : ℕ) (arcs : List ResArc) (D : Array (Option ℤ)) :
    StateM Cost (Array (Option ℤ) × Array (Option ResArc)) := do
  let mut D' : Array (Option ℤ) := Array.replicate N none
  let mut P : Array (Option ResArc) := Array.replicate N none
  for a in arcs do
    tick 1
    match D.getD a.src none with
    | none => pure ()
    | some d =>
      let cand ← zadd d a.cost
      match D'.getD a.dst none with
      | none =>
        D' := D'.set! a.dst (some cand)
        P := P.set! a.dst (some a)
      | some cur =>
        if ← zlt cand cur then
          D' := D'.set! a.dst (some cand)
          P := P.set! a.dst (some a)
  pure (D', P)

end FlowAllocationGames.UnitRanking


