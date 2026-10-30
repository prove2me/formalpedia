-- Prove2me | Definitions.Def_Timetabling_CT4_LocallyFeasible
-- name    : Timetabling_CT4_LocallyFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:32:56.070359+00:00
-- url     : https://prove2.me/theorems/84f1b442-25be-4894-bd62-ac262b13b2d1
-- title:
--   Possible schedule of one teacher
-- statement:
--   Fix a CT4 instance and a teacher $t_j$. A 0/1 array $y_{ik}$ ($y_{ik} = 1$: $t_j$ meets class $c_i$ at period $k$) is a **possible schedule** of $t_j$ when it satisfies every constraint of CT4 that involves $t_j$ alone:
--
--   1. (12) $\sum_{k} y_{ik} = \bar r_{ij}$ for every class $c_i$;
--   2. (14) $\sum_{i} y_{ik} \le \bar c_{jk}$ for every period $k$;
--   3. (15) every $y_{ik}$ is $0$ or $1$;
--   4. (13) for $t_j$ alone: $y_{ik} = 1$ only if $\bar b_{ik} = 1$.
--
--   The slice $k \mapsto \bar x_{ijk}$ of a timetable is a possible schedule of $t_j$. The only constraint that couples different teachers is (13), which forbids two teachers from meeting the same class in the same period; that is what the conflict graph records.
-- source:
--   de Werra (1985), proof of Proposition 2.4, pp. 154-155, "possible schedules"; constraints (12)-(15), p. 154. D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_CT4_Instance

namespace Timetabling.CT4

open Finset

/-- **A possible schedule of one teacher, as a 0/1 slice.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4,
pp. 154–155: "each teacher has exactly 2 possible schedules", and Sec. 2.2, p. 154,
constraints (12)–(15).

`y i k = 1` means that teacher `t_j` meets class `c_i` at period `k`. The slice `y` is a possible
schedule of `t_j` when it satisfies every constraint of CT4 that involves teacher `t_j` alone:

* (12) `∑_k y_ik = r̄_ij` for every class `i`;
* (14) `∑_i y_ik ≤ c̄_jk` for every period `k`;
* (15) every `y_ik` is `0` or `1`;
* (13) restricted to `t_j`: `y_ik = 1` only when `b̄_ik = 1`.

**Formalization Note.** These are exactly the constraints on the slice `x̄_{·j·}` of a timetable;
constraint (13) also couples different teachers, which is what the conflict graph records. -/
def LocallyFeasible {m n p : ℕ} (I : Instance m n p) (j : Fin n) (y : Fin m → Fin p → ℕ) :
    Prop :=
  (∀ i, ∑ k, y i k = I.rbar i j) ∧
  (∀ k, ∑ i, y i k ≤ I.cbar j k) ∧
  (∀ i k, y i k = 0 ∨ y i k = 1) ∧
  (∀ i k, y i k = 1 → I.bbar i k = 1)

end Timetabling.CT4


