-- Prove2me | Definitions.Def_Timetabling_CT4_pickSched
-- name    : Timetabling_CT4_pickSched
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:35:40.412991+00:00
-- url     : https://prove2.me/theorems/2a30abf1-d882-4481-a497-1f24824396c0
-- title:
--   Schedule attached to node $x_j$ or $\bar x_j$
-- statement:
--   From the list $S$ of a teacher's possible schedules, node $x_j$ receives the first schedule and node $\bar x_j$ the second. When there is a single schedule both nodes receive it; when there is none both receive the empty schedule.
--
--   **Formalization Note** The duplicate keeps $2n$ nodes in the conflict graph when a teacher has a single possible schedule (the printed "exactly 2" is corrected to "at most 2"). The empty case does not occur where the graph is used.
-- source:
--   de Werra (1985), proof of Proposition 2.4, p. 155, "For teacher t_j introduce 2 nodes x_j, x̄_j corresponding to his possible schedules". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib

namespace Timetabling.CT4

/-- **The schedule attached to node `x_j` or `x̄_j`.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4, p. 155:
"For teacher t_j introduce 2 nodes x_j, x̄_j corresponding to his possible schedules".

From the list `S` of a teacher's schedules, `pickSched S true` is the first one (node `x_j`) and
`pickSched S false` the second (node `x̄_j`). When there is only one schedule both nodes carry it;
when there is none both carry the empty list.

**Formalization Note.** The duplicate keeps `2n` nodes when a teacher has a single schedule
(the printed "exactly 2" is corrected to "at most 2" in `teacherSchedules_spec`). The empty case
does not occur on the instances where the conflict graph is used. -/
def pickSched {m p : ℕ} (S : List (List (Fin m × Fin p))) (b : Bool) : List (Fin m × Fin p) :=
  match S with
  | [] => []
  | [s] => s
  | s :: t :: _ => if b then s else t

end Timetabling.CT4


