-- Prove2me | Definitions.Def_Timetabling_StableHalf_firstOpen
-- name    : Timetabling_StableHalf_firstOpen
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:30:13.609988+00:00
-- url     : https://prove2.me/theorems/75a88c4a-b66d-4a63-b2ce-938edbc1695d
-- title:
--   The next open pair
-- statement:
--   Given a partial assignment $a$ of the pairs $1, \dots, n$, $\mathsf{firstOpen}(a)$ scans the pairs in increasing order, one tick per pair, and returns the lowest-index pair $j$ that is still open, or reports that every pair is assigned.
--
--   It selects the teacher on which the limited backtracking of Proposition 2.4 takes its next decision ("there are still some teachers whose schedule is not fixed, then we [...] take a new decision").
--
--   **Formalization Note** The page chooses the teacher arbitrarily; the lowest open index is taken. The scan costs $n$ ticks.
-- source:
--   de Werra (1985), proof of Proposition 2.4, p. 155, "If we have taken all implications into account and there are still some teachers whose schedule is not fixed, then we consider the last decision as permanent and take a new decision". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_Cost_tick

namespace Timetabling.StableHalf

/-- **The next pair on which to take a decision.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4, p. 155:
"there are still some teachers whose schedule is not fixed, then we [...] take a new decision".

Scans the pairs `0, 1, …, n − 1` in order, one tick per pair, and returns the lowest-index pair
`j` with `a j = none`, or `none` when every pair is assigned.

**Formalization Note.** The page leaves the choice of the next teacher free ("one arbitrary
selects"); the lowest open index is taken. The scan costs `n` ticks. -/
def firstOpen {n : ℕ} (a : Fin n → Option Bool) : StateM ℕ (Option (Fin n)) :=
  (List.finRange n).foldlM
    (fun acc j => do
      Cost.tick
      pure (acc <|> if (a j).isNone then some j else none))
    none

end Timetabling.StableHalf


