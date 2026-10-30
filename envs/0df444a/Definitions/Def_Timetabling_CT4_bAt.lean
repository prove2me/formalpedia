-- Prove2me | Definitions.Def_Timetabling_CT4_bAt
-- name    : Timetabling_CT4_bAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:34:34.046097+00:00
-- url     : https://prove2.me/theorems/52bcff2f-dedb-4781-a121-e7dfc2ada6ef
-- title:
--   Ticked read of a class's availability
-- statement:
--   $\mathsf{bAt}(I, i, k)$ costs one tick and returns $\bar b_{ik}$ ($1$ if class $c_i$ is available and not preassigned at period $k$, $0$ otherwise).
--
--   Algorithms read the input of CT4 only through $\mathsf{availAt}$, $\mathsf{lectureAt}$ and $\mathsf{bAt}$, one tick per read.
-- source:
--   de Werra (1985), Sec. 2.2, p. 154, definition of b̄_ik. D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_Cost_tick
import Definitions.Def_Timetabling_CT4_Instance

namespace Timetabling.CT4

/-- **Ticked read of a class's availability.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), Sec. 2.2, p. 154, `b̄_ik`.

`bAt I i k` costs one tick and returns `b̄_ik`.

**Formalization Note.** Algorithms read the input only through `availAt`, `lectureAt` and
`bAt`, one tick per read. -/
def bAt {m n p : ℕ} (I : Instance m n p) (i : Fin m) (k : Fin p) : StateM ℕ ℕ := do
  Cost.tick
  pure (I.bbar i k)

end Timetabling.CT4


