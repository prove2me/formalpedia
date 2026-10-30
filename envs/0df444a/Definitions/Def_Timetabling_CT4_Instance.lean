-- Prove2me | Definitions.Def_Timetabling_CT4_Instance
-- name    : Timetabling_CT4_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:31:25.036557+00:00
-- url     : https://prove2.me/theorems/d20c8dd3-d9d6-410e-9e80-eb683e808561
-- title:
--   Instance of the class-teacher timetabling problem CT4
-- statement:
--   An instance of **CT4** (class-teacher timetabling with preassignments and unavailabilities) has $m$ classes $c_1, \dots, c_m$, $n$ teachers $t_1, \dots, t_n$ and $p$ periods $1, \dots, p$; every lecture lasts one period. Its data are:
--
--   1. $\bar r_{ij}$: the number of lectures of class $c_i$ with teacher $t_j$ that remain to be scheduled ($\bar r_{ij} = r_{ij} - \sum_k p_{ijk}$, preassigned lectures removed);
--   2. $\bar b_{ik} = 1$ if class $c_i$ is available and not preassigned at period $k$, $0$ otherwise;
--   3. $\bar c_{jk} = 1$ if teacher $t_j$ is available and not preassigned at period $k$, $0$ otherwise;
--   4. for every teacher $t_j$, the list of periods at which $t_j$ is available (those $k$ with $\bar c_{jk} = 1$);
--   5. for every teacher $t_j$, the list of classes $t_j$ must meet, class $c_i$ listed $\bar r_{ij}$ times.
--
--   Items 4 and 5 are the presentation of Table 1 of the paper ("Available at periods", "Must meet classes").
--
--   **Formalization Note** Indices are 0-based (`Fin m`, `Fin n`, `Fin p`). The two lists are the same data as the arrays, rearranged; `WellFormed` ties them together. They are part of the input because the time bound of Proposition 2.4 does not depend on $m$ or $p$: with only the arrays, an algorithm must search the $p$ entries of $\bar c_{j\cdot}$ to find a teacher's free period.
-- source:
--   de Werra (1985), Sec. 2.1, p. 152, and Sec. 2.2, p. 154 (data of constraints (12)-(15)); Table 1, p. 155. D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib

namespace Timetabling.CT4

/-- **An instance of the class-teacher timetabling problem CT4.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), Sec. 2.1, p. 152 (classes
`c_1, …, c_m`, teachers `t_1, …, t_n`, periods `1, …, p`), Sec. 2.2, p. 154 (the data
`r̄_ij`, `b̄_ik`, `c̄_jk` of constraints (12)–(15)) and Table 1, p. 155 ("Available at periods",
"Must meet classes").

* `rbar i j = r̄_ij`: number of lectures of class `c_i` with teacher `t_j` still to be scheduled;
* `bbar i k = b̄_ik`: `1` if class `c_i` is available and not preassigned at period `k`, else `0`;
* `cbar j k = c̄_jk`: `1` if teacher `t_j` is available and not preassigned at period `k`, else `0`;
* `avail j`: the periods `k` with `c̄_jk = 1`, as a list;
* `lectures j`: the classes teacher `t_j` must meet, class `c_i` listed `r̄_ij` times.

**Formalization Note.** Indices are 0-based (`Fin m`, `Fin n`, `Fin p`). The two lists are the
per-teacher presentation of Table 1; `WellFormed` ties them to the arrays, so they are the same
data rearranged. They are part of the input because the `O(n^2)` bound does not depend on `m`
or `p`. -/
structure Instance (m n p : ℕ) where
  rbar : Fin m → Fin n → ℕ
  bbar : Fin m → Fin p → ℕ
  cbar : Fin n → Fin p → ℕ
  avail : Fin n → List (Fin p)
  lectures : Fin n → List (Fin m)

end Timetabling.CT4


