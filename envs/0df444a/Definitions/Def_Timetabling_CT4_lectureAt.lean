-- Prove2me | Definitions.Def_Timetabling_CT4_lectureAt
-- name    : Timetabling_CT4_lectureAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:34:05.051418+00:00
-- url     : https://prove2.me/theorems/1343845d-180e-4db4-ab28-08fe98b7e50c
-- title:
--   Ticked read of the classes a teacher must meet
-- statement:
--   $\mathsf{lectureAt}(I, j, r)$ costs one tick and returns the $r$-th entry (counting from $0$) of the list of classes teacher $t_j$ must meet, or nothing if the list is shorter.
--
--   Algorithms read the input of CT4 only through $\mathsf{availAt}$, $\mathsf{lectureAt}$ and $\mathsf{bAt}$, one tick per read.
-- source:
--   de Werra (1985), Table 1, p. 155, column "Must meet classes". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_Cost_tick
import Definitions.Def_Timetabling_CT4_Instance

namespace Timetabling.CT4

/-- **Ticked read of the classes a teacher must meet.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), Table 1, p. 155, column "Must meet
classes".

`lectureAt I j r` costs one tick and returns the `r`-th entry (0-based) of `I.lectures j`, or
`none` if the list is shorter.

**Formalization Note.** Algorithms read the input only through `availAt`, `lectureAt` and
`bAt`, one tick per read. -/
def lectureAt {m n p : ℕ} (I : Instance m n p) (j : Fin n) (r : ℕ) :
    StateM ℕ (Option (Fin m)) := do
  Cost.tick
  pure (I.lectures j)[r]?

end Timetabling.CT4


