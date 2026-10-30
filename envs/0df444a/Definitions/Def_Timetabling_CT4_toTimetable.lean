-- Prove2me | Definitions.Def_Timetabling_CT4_toTimetable
-- name    : Timetabling_CT4_toTimetable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:38:42.226612+00:00
-- url     : https://prove2.me/theorems/d0e83929-e1fe-4ec1-9156-ac727dc2cdc2
-- title:
--   Reading a list of meetings as the variables $\bar x_{ijk}$
-- statement:
--   A list $L$ of triples $(i, j, k)$ (class, teacher, period) defines
--
--   $$
--   \bar x_{ijk} = \begin{cases} 1 & \text{if } (i, j, k) \in L, \\ 0 & \text{otherwise.} \end{cases}
--   $$
--
--   The algorithm of Proposition 2.4 outputs its timetable as such a list, of length at most $2n$, which is how it can be written down in $O(n)$ time.
-- source:
--   de Werra (1985), Sec. 2.2, p. 154, definition of x̄_ijk. D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib

namespace Timetabling.CT4

/-- **Reading an output list as the variables `x̄_ijk`.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), Sec. 2.2, p. 154: "x̄_ijk = 1 if
class c_i and teacher t_j meet at period k [...] and x̄_ijk = 0 otherwise".

A list `L` of triples `(i, j, k)` (class, teacher, period) defines `x̄_ijk = 1` if `(i, j, k)`
occurs in `L` and `0` otherwise.

**Formalization Note.** The timetabling algorithm outputs its timetable as such a list, of
length at most `2n`. -/
def toTimetable {m n p : ℕ} (L : List (Fin m × Fin n × Fin p)) : Fin m → Fin n → Fin p → ℕ :=
  fun i j k => if (i, j, k) ∈ L then 1 else 0

end Timetabling.CT4


