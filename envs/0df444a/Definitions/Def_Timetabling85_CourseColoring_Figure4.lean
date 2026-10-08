-- Prove2me | Definitions.Def_Timetabling85_CourseColoring_Figure4
-- name    : Timetabling85_CourseColoring_Figure4
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:13.464983+00:00
-- url     : https://prove2.me/theorems/26c0c8c6-c387-4a0a-993e-1bdf91355047
-- title:
--   §3.1, Figure 4, p. 157 — three courses with 1, 2, 2 lectures, two students, and the printed schedule in 4 periods
-- statement:
--   The example of Figure 4 in §3.1.
--
--   There are three courses $K_1, K_2, K_3$ with $1, 2, 2$ lectures; student 1 takes $K_1$ and $K_2$, student 2 takes $K_2$ and $K_3$. The schedule corresponding to the colouring in Figure 4 uses $p = 4$ periods:
--
--   | period | lectures |
--   |---|---|
--   | 1 | the lecture of $K_1$ and the first lecture of $K_3$ |
--   | 2 | the first lecture of $K_2$ |
--   | 3 | the second lecture of $K_2$ |
--   | 4 | the second lecture of $K_3$ |
--
--   This is the data on which the construction of §3.1 is illustrated.
--
--   **Formalization Note** Courses, students and periods are indexed from $0$: course $K_j$ is index $j-1$ and period $j$ is index $j-1$. The page lists the schedule by period ("1 lecture of $K_3$") without naming which lecture; the first lecture of each course is put at the earlier period, which is the colouring of Figure 4 ($m_{11}=1$, $m_{21}=2$, $m_{22}=3$, $m_{31}=1$, $m_{32}=4$).
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), p. 157, §3.1, Figure 4 and the data and schedule printed under it

import Mathlib
import Definitions.Def_Timetabling85_CourseColoring_CSUP

namespace Timetabling85.CourseColoring

/-- The data of Figure 4 (§3.1, p. 157), with courses and students indexed from `0`: courses
`K_1, K_2, K_3` (indices `0, 1, 2`) with `1, 2, 2` lectures; student 1 (index `0`) takes `K_1`
and `K_2`, student 2 (index `1`) takes `K_2` and `K_3`. -/
def figure4 : CourseInstance 3 2 where
  lectures := ![1, 2, 2]
  takes := ![{0, 1}, {1, 2}]

/-- The schedule corresponding to the colouring in Figure 4, in `p = 4` periods indexed from `0`
(period `j` of the page is `j - 1` here): period 1 holds the lecture of `K_1` and the first
lecture of `K_3`; period 2 the first lecture of `K_2`; period 3 the second lecture of `K_2`;
period 4 the second lecture of `K_3`. -/
def figure4Schedule : figure4.Lecture → Fin 4 := fun l =>
  if l.1 = 0 then 0
  else if l.1 = 1 then (if l.2.val = 0 then 1 else 2)
  else (if l.2.val = 0 then 0 else 3)

end Timetabling85.CourseColoring


