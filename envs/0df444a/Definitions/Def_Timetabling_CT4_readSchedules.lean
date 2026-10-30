-- Prove2me | Definitions.Def_Timetabling_CT4_readSchedules
-- name    : Timetabling_CT4_readSchedules
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:37:39.481632+00:00
-- url     : https://prove2.me/theorems/663b826b-ce85-4db3-b034-981b1019eb3c
-- title:
--   Computing a teacher's schedules in constant time
-- statement:
--   For teacher $t_j$, $\mathsf{readSchedules}(I, j)$ reads, one tick each, the first two entries of $t_j$'s available periods, the first three entries of the classes $t_j$ must meet, and $\bar b_{ik}$ for each class $c_i$ among the first two lectures and each period $k$ among the first two available periods. If there is a third lecture, the result is the empty list (more lectures than free periods: no possible schedule). Otherwise the result is the list of placements of the lectures read on the periods read ($\mathsf{schedulesFrom}$), using the $\bar b$ values read.
--
--   It costs at most $10$ ticks, independently of $m$, $p$ and the length of the lists, and is how the algorithm of Proposition 2.4 builds the nodes of the conflict graph.
-- source:
--   de Werra (1985), proof of Proposition 2.4, pp. 154-155, "each teacher has exactly 2 possible schedules"; Table 1, p. 155. D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_CT4_availAt
import Definitions.Def_Timetabling_CT4_lectureAt
import Definitions.Def_Timetabling_CT4_bAt
import Definitions.Def_Timetabling_CT4_schedulesFrom

namespace Timetabling.CT4

/-- **Computing a teacher's schedules in `O(1)` time.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4,
pp. 154–155 ("each teacher has exactly 2 possible schedules") and Table 1, p. 155.

For teacher `t_j`, read (one tick each) the first 2 entries of `avail j`, the first 3 entries
of `lectures j`, and `b̄_ik` for every class `i` among the first 2 lectures and every period `k`
among the first 2 free periods. If a third lecture exists the result is `[]` (more lectures than
free periods: no schedule). Otherwise the result is `schedulesFrom` applied to the lectures and
periods read, with the `b̄` values read.

**Formalization Note.** At most `1 + 2 + 3 + 4 = 10` ticks, whatever `m`, `p` and the lengths of
the lists. For a well-formed instance in which `t_j` is free in at most 2 periods the result is
`teacherSchedules I j` (milestone `ct4_build_and_query_cost`). -/
def readSchedules {m n p : ℕ} (I : Instance m n p) (j : Fin n) :
    StateM ℕ (List (List (Fin m × Fin p))) := do
  Cost.tick
  let a₀ ← availAt I j 0
  let a₁ ← availAt I j 1
  let l₀ ← lectureAt I j 0
  let l₁ ← lectureAt I j 1
  let l₂ ← lectureAt I j 2
  match l₂ with
  | some _ => pure []
  | none =>
    let A := a₀.toList ++ a₁.toList
    let L := l₀.toList ++ l₁.toList
    let reads ← (L.flatMap fun i => A.map fun k => (i, k)).mapM fun ik => do
      let v ← bAt I ik.1 ik.2
      pure (ik, v)
    let ok : Fin m → Fin p → Bool := fun i k => reads.any fun r => r.1 = (i, k) && r.2 == 1
    pure (schedulesFrom ok L A)

end Timetabling.CT4


