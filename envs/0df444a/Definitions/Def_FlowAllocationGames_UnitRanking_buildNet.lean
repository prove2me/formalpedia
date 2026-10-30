-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_buildNet
-- name    : FlowAllocationGames_UnitRanking_buildNet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:25:31.910363+00:00
-- url     : https://prove2.me/theorems/e23eb48b-d00b-4b49-b4df-f8b421311e66
-- title:
--   Building $G'$ from a game
-- statement:
--   Builds the circulation network $G'$ of a game: nodes $0, \dots, n$ with $s = n$; edges, in this order, the $m$ edges of $G$ with capacities $c_e$, the edges $(v, s)$ with capacity $U = \sum_v b_v$, and the edges $(s, v)$ with capacity $b_v$. Every input entry is read through the ticked accessors.
--
--   The infinite capacity of $(v, s)$ is replaced by $U$, which removes no circulation: in every circulation $x_{(v,s)} \le \sum_w x_{(w,s)} = \sum_w x_{(s,w)} \le U$.
--
--   This is part of the witness algorithm of the mission: the paper computes the optimal circulation $f^*$ by citing Tardos [45] and fixes no algorithm.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §3.1, p. 17

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_Cost
import Definitions.Def_FlowAllocationGames_UnitRanking_tick
import Definitions.Def_FlowAllocationGames_UnitRanking_zadd
import Definitions.Def_FlowAllocationGames_UnitRanking_bAt
import Definitions.Def_FlowAllocationGames_UnitRanking_cAt
import Definitions.Def_FlowAllocationGames_UnitRanking_tailAt
import Definitions.Def_FlowAllocationGames_UnitRanking_headAt
import Definitions.Def_FlowAllocationGames_UnitRanking_Net

namespace FlowAllocationGames.UnitRanking

/-- **Building `G′` from a game.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, §3.1, p. 17: "We add
to G an auxiliary node s. For every v ∈ V, we add an auxiliary edge (v, s) with capacity
c(v,s) = ∞. For every v ∈ V with bv > 0 we add an auxiliary edge (s, v) with c(s,v) = bv".

The nodes of `G′` are `0, …, n` with `s = n`. Its edges are, in this order: the `m` edges of `G`
with capacities `c e`; the edges `(v, s)` for `v = 0, …, n - 1`, with capacity `U = Σ_v b v`; the
edges `(s, v)` for `v = 0, …, n - 1`, with capacity `b v`. Every input entry is read through the
ticked accessors.

**Formalization Note.** The infinite capacity of `(v, s)` is replaced by `U`. This removes no
circulation: in every circulation, `toS v ≤ Σ toS = Σ fromS ≤ Σ b = U`. An edge `(s, v)` with
`b v = 0` has capacity `0` and carries no flow. -/
def buildNet {n m : ℕ} (Γ : Game n m) : StateM Cost Net := do
  let mut U : ℤ := 0
  for v in List.finRange n do
    tick 1
    let bv ← bAt Γ v
    U ← zadd U bv
  let mut tl : Array ℕ := #[]
  let mut hd : Array ℕ := #[]
  let mut cap : Array ℤ := #[]
  for e in List.finRange m do
    tick 1
    let t ← tailAt Γ e
    let h ← headAt Γ e
    let ce ← cAt Γ e
    tl := tl.push t
    hd := hd.push h
    cap := cap.push ce
  for v in List.finRange n do
    tick 1
    tl := tl.push v
    hd := hd.push n
    cap := cap.push U
  for v in List.finRange n do
    tick 1
    let bv ← bAt Γ v
    tl := tl.push n
    hd := hd.push v
    cap := cap.push bv
  pure ⟨n + 1, tl, hd, cap⟩

end FlowAllocationGames.UnitRanking


