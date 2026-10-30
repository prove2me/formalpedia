-- Prove2me | Definitions.Def_Timetabling_CT4_teacherSchedules
-- name    : Timetabling_CT4_teacherSchedules
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:35:26.17435+00:00
-- url     : https://prove2.me/theorems/76bc341d-292e-40b0-aae4-6025ea207126
-- title:
--   The possible schedules of a teacher
-- statement:
--   For a CT4 instance and a teacher $t_j$, $\mathsf{teacherSchedules}(I, j)$ lists, once per set of slots, the ways of meeting every class on $t_j$'s list at pairwise distinct periods at which $t_j$ is available and the class is free ($\bar b_{ik} = 1$).
--
--   For the instance of Table 1 these are exactly the schedules printed on p. 155 ("for each $t_i$ we have the following schedules"), in the printed order: the first is node $x_j$, the second node $\bar x_j$. The milestone *at most two schedules per teacher* shows that, on a well-formed instance, these are the slot sets of the possible schedules of $t_j$, and that there are at most two of them when $t_j$ is free in at most two periods.
-- source:
--   de Werra (1985), proof of Proposition 2.4, pp. 154-155, "each teacher has exactly 2 possible schedules"; schedule table, p. 155. D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_CT4_Instance
import Definitions.Def_Timetabling_CT4_schedulesFrom

namespace Timetabling.CT4

/-- **The possible schedules of a teacher.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4,
pp. 154–155: "each teacher has exactly 2 possible schedules", and the table of schedules on
p. 155 ("for each t_i we have the following schedules").

`teacherSchedules I j` lists, once per set of slots, the ways of meeting every class of
`I.lectures j` at pairwise distinct periods of `I.avail j` at which the class is free
(`b̄_ik = 1`). A schedule is a list of slots `(i, k)`: teacher `t_j` meets class `c_i` at period
`k`.

**Formalization Note.** The milestone `teacherSchedules_spec` shows that, for a well-formed
instance, these are exactly the slot sets of the possible schedules (`LocallyFeasible`) and that
there are at most 2 of them when the teacher is free in at most 2 periods. -/
def teacherSchedules {m n p : ℕ} (I : Instance m n p) (j : Fin n) :
    List (List (Fin m × Fin p)) :=
  schedulesFrom (fun i k => decide (I.bbar i k = 1)) (I.lectures j) (I.avail j)

end Timetabling.CT4


