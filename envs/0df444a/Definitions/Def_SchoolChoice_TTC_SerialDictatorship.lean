-- Prove2me | Definitions.Def_SchoolChoice_TTC_SerialDictatorship
-- name    : SchoolChoice_TTC_SerialDictatorship
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T07:22:50.768383+00:00
-- url     : https://prove2.me/theorems/62b3c26a-aa26-44dd-958f-aeb0f56e798c
-- title:
--   Serial dictatorship induced by a priority ordering
-- statement:
--   Given capacities $q=(q_s)_{s\in S}$, a strict ordering $\pi$ of the students and a preference profile $P$, the **serial dictatorship** induced by $\pi$ processes the students one at a time in the order $\pi$ (highest-ranked first). Each student in turn is assigned her favourite school, under $P_i$, among the schools that still have a free seat, and that school loses one seat.
--
--   Formally, starting from the seat counts $c_s = q_s$, the student $i$ whose turn it is receives
--   $$\sigma(i) = \text{the } P_i\text{-best school } s \text{ with } c_s>0, \qquad c_{\sigma(i)} \leftarrow c_{\sigma(i)}-1 .$$
--
--   The paper remarks that the top trading cycles mechanism reduces to this mechanism when all schools share one priority ordering.
--
--   **Formalization Note** The output is an `Option S` per student; if no school had a free seat at a student's turn she would receive `none` and the seat counts would stay unchanged. Under the no-shortage assumption $|I|\le\sum_s q_s$ this never happens.
-- source:
--   Abdulkadiroğlu and Sönmez, School Choice: A Mechanism Design Approach, Columbia Univ. Economics Discussion Paper No. 0203-18 (July 2003), p. 16, Section II.B (serial dictatorship)

import Mathlib
import Definitions.Def_SchoolChoice_TTC_Algorithm

namespace SchoolChoice.TTC

variable {I S : Type} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]

/-- One turn of the serial dictatorship: the state is a pair (counters, assignment);
student `i` takes her favourite school under `P i` among the schools with a positive
counter, whose counter then drops by one. If no school has a seat left, nothing changes. -/
def sdTurn (P : I → Pref S) (acc : (S → ℕ) × (I → Option S)) (i : I) :
    (S → ℕ) × (I → Option S) :=
  match bestIn (P i) (Finset.univ.filter (fun s => 0 < acc.1 s)) with
  | none => acc
  | some s => (Function.update acc.1 s (acc.1 s - 1), Function.update acc.2 i (some s))

/-- The serial dictatorship induced by the priority ordering `π` (Section II.B, p. 16):
the student ranked first by `π` is assigned her top choice, the next student her top
choice among the remaining seats, and so on, starting from the capacities `q`. The value
`none` would mean that a student found no seat left. -/
def serialDictatorship (q : S → ℕ) (π : Priority I) (P : I → Pref S) : I → Option S :=
  (((List.finRange (Fintype.card I)).map π.symm).foldl (sdTurn P) (q, fun _ => none)).2

end SchoolChoice.TTC


