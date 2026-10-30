-- Prove2me | Definitions.Def_Timetabling_CT4_availAt
-- name    : Timetabling_CT4_availAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:33:28.994135+00:00
-- url     : https://prove2.me/theorems/2cd11a1b-77ee-45d1-b387-10c45488bb17
-- title:
--   Ticked read of a teacher's available periods
-- statement:
--   $\mathsf{availAt}(I, j, r)$ costs one tick and returns the $r$-th entry (counting from $0$) of the list of periods at which teacher $t_j$ is available, or nothing if the list is shorter.
--
--   Algorithms read the input of CT4 only through $\mathsf{availAt}$, $\mathsf{lectureAt}$ and $\mathsf{bAt}$, one tick per read, so their tick count bounds their running time.
-- source:
--   de Werra (1985), Table 1, p. 155, column "Available at periods". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_Cost_tick
import Definitions.Def_Timetabling_CT4_Instance

namespace Timetabling.CT4

/-- **Ticked read of a teacher's available periods.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), Table 1, p. 155, column "Available
at periods".

`availAt I j r` costs one tick and returns the `r`-th entry (0-based) of `I.avail j`, or `none`
if the list is shorter.

**Formalization Note.** Algorithms read the input only through `availAt`, `lectureAt` and
`bAt`, one tick per read (the cost model of `Timetabling.Cost.tick`). -/
def availAt {m n p : ℕ} (I : Instance m n p) (j : Fin n) (r : ℕ) : StateM ℕ (Option (Fin p)) := do
  Cost.tick
  pure (I.avail j)[r]?

end Timetabling.CT4


