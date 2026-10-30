-- Prove2me | Definitions.Def_Timetabling_CT4_ct4Solve
-- name    : Timetabling_CT4_ct4Solve
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:39:45.109718+00:00
-- url     : https://prove2.me/theorems/bc35c132-c595-4c57-9348-c8aec677c3cd
-- title:
--   The algorithm of Proposition 2.4
-- statement:
--   Given a CT4 instance $I$, the algorithm $\mathsf{ct4Solve}$:
--
--   1. for every teacher $t_j$ (one tick each), computes $t_j$'s possible schedules with $\mathsf{readSchedules}$ (constant time); if some teacher has none, it reports that no timetable exists;
--   2. runs the limited backtracking $\mathsf{stableHalf}$ on the conflict graph $G$, queried through $\mathsf{compat}$; if it reports failure, so does the algorithm;
--   3. otherwise, from the returned choice $c$, outputs for every teacher $t_j$ (one tick each) the meetings $(i, j, k)$ of the schedule of node $(j, c_j)$.
--
--   The output is a list of triples, read as $\bar x$ through $\mathsf{toTimetable}$, or the report that no timetable exists. Proposition 2.4 states that this is correct and runs in $O(n^2)$ time.
--
--   **Formalization Note** The input is read only through the ticked accessors, so the tick count is the running time in the unit-cost RAM model.
-- source:
--   de Werra (1985), Proposition 2.4, p. 154, and proof, pp. 154-155. D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_StableHalf_stableHalf
import Definitions.Def_Timetabling_CT4_compat

namespace Timetabling.CT4

/-- **The algorithm of Proposition 2.4.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), Proposition 2.4, p. 154, and its
proof, pp. 154–155: "there is an O(n^2) algorithm for finding a timetable (or showing that none
exists)".

1. For every teacher `t_j` (one tick each), compute its schedules (`readSchedules`, `O(1)`
   ticks). If some teacher has none, return `none`.
2. Run the limited backtracking `stableHalf` on the conflict graph, queried through the
   adjacency test `compat I`. If it returns `none`, return `none`.
3. From its choice `c`, output, for every teacher `t_j` (one tick each, schedules recomputed in
   `O(1)` ticks), the triples `(i, j, k)` of the schedule of node `(j, c j)`.

**Formalization Note.** The output list is read as a timetable through `toTimetable`. The input
is read only through the ticked accessors, so the tick count is the running time in the
unit-cost RAM model. -/
def ct4Solve {m n p : ℕ} (I : Instance m n p) :
    StateM ℕ (Option (List (Fin m × Fin n × Fin p))) := do
  let allHave ← (List.finRange n).foldlM
    (fun acc j => do
      Cost.tick
      let S ← readSchedules I j
      pure (acc && !S.isEmpty))
    true
  if !allHave then pure none
  else do
    let r ← StableHalf.stableHalf (compat I)
    match r with
    | none => pure none
    | some c => do
      let out ← (List.finRange n).foldlM
        (fun acc j => do
          Cost.tick
          let S ← readSchedules I j
          pure ((pickSched S (c j)).map (fun ik => (ik.1, j, ik.2)) ++ acc))
        []
      pure (some out)

end Timetabling.CT4


