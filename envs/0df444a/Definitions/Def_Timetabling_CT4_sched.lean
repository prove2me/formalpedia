-- Prove2me | Definitions.Def_Timetabling_CT4_sched
-- name    : Timetabling_CT4_sched
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:36:25.749575+00:00
-- url     : https://prove2.me/theorems/72f0279c-e906-4e7c-9c9a-00aa4da9ded8
-- title:
--   Schedule of a node of the conflict graph
-- statement:
--   For a CT4 instance, the node $x_j$ (resp. $\bar x_j$) of the conflict graph corresponds to the first (resp. second) possible schedule of teacher $t_j$; $\mathsf{sched}(I, v)$ is the schedule of node $v$, as a list of slots $(i, k)$. A teacher with a single possible schedule has it on both nodes.
-- source:
--   de Werra (1985), proof of Proposition 2.4, p. 155, "For teacher t_j introduce 2 nodes x_j, x̄_j corresponding to his possible schedules". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_CT4_teacherSchedules
import Definitions.Def_Timetabling_CT4_pickSched

namespace Timetabling.CT4

/-- **The schedule of a node of the conflict graph.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4, p. 155:
"For teacher t_j introduce 2 nodes x_j, x̄_j corresponding to his possible schedules".

The node `(j, true)` is `x_j` and `(j, false)` is `x̄_j`; `sched I (j, b)` is the corresponding
schedule of teacher `t_j`, taken from `teacherSchedules I j` by `pickSched`.

**Formalization Note.** A teacher with a single schedule has it on both nodes. -/
def sched {m n p : ℕ} (I : Instance m n p) (v : Fin n × Bool) : List (Fin m × Fin p) :=
  pickSched (teacherSchedules I v.1) v.2

end Timetabling.CT4


