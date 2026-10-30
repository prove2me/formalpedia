-- Prove2me | Definitions.Def_Timetabling_CT4_compat
-- name    : Timetabling_CT4_compat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:38:29.218948+00:00
-- url     : https://prove2.me/theorems/fd2501b6-5e0b-4dd1-a93f-956069227708
-- title:
--   Adjacency test of the conflict graph
-- statement:
--   $\mathsf{compat}(I, u, w)$ answers whether nodes $u$ and $w$ of the conflict graph are linked. It ticks once; answers *no* if $u = w$ and *yes* if $u$, $w$ are the two nodes of one teacher; otherwise it computes the schedules of both teachers ($\mathsf{readSchedules}$), takes the schedules of $u$ and $w$, and compares them slot by slot (one tick per comparison, at most four comparisons), answering *yes* when they share a slot.
--
--   It is the adjacency oracle on which the algorithm of Proposition 2.4 runs the limited backtracking; each query costs a bounded number of ticks.
-- source:
--   de Werra (1985), proof of Proposition 2.4, p. 155, "we link 2 nodes in G if the corresponding schedules are not compatible". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_CT4_readSchedules
import Definitions.Def_Timetabling_CT4_pickSched

namespace Timetabling.CT4

/-- **The adjacency test of the conflict graph, in `O(1)` time.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4, p. 155:
"we link 2 nodes in G if the corresponding schedules are not compatible (in particular, nodes
x_j and x̄_j are linked)".

`compat I u w` ticks once; it answers `false` when `u = w` and `true` when `u`, `w` are the two
nodes of one teacher. Otherwise it computes both teachers' schedules (`readSchedules`), takes the
schedules of `u` and `w` (`pickSched`) and compares them slot by slot, one tick per comparison,
answering `true` when they share a slot.

**Formalization Note.** For a well-formed instance with every teacher free in at most 2 periods
this answers the adjacency of `conflictGraph I` within a constant number of ticks (milestone
`ct4_build_and_query_cost`). -/
def compat {m n p : ℕ} (I : Instance m n p) (u w : Fin n × Bool) : StateM ℕ Bool := do
  Cost.tick
  if u = w then pure false
  else if u.1 = w.1 then pure true
  else do
    let Su ← readSchedules I u.1
    let Sw ← readSchedules I w.1
    let su := pickSched Su u.2
    let sw := pickSched Sw w.2
    su.foldlM (fun acc x => sw.foldlM (fun acc' y => do
      Cost.tick
      pure (acc' || decide (x = y))) acc) false

end Timetabling.CT4


