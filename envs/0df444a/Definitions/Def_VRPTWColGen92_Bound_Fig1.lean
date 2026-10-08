-- Prove2me | Definitions.Def_VRPTWColGen92_Bound_Fig1
-- name    : VRPTWColGen92_Bound_Fig1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:24:14.096326+00:00
-- url     : https://prove2.me/theorems/a2b8a4f0-e31a-4e61-8bd2-27b006fc939e
-- title:
--   Figure 1, p. 345 — the four-node example instance (Q = 6)
-- statement:
--   This module records the four-node example of Figure 1 of Desrochers, Desrosiers and Solomon (1992), used in Sec. 3 to compare the solution spaces of the three subproblem models.
--
--   The nodes are the depot $d$ and the customers $1, 2, 3$; the vehicle capacity is $Q = 6$. Demands and windows:
--
--   | node | $q$ | $[a, b]$ |
--   |---|---|---|
--   | $d$ | $0$ | $[0, 8]$ |
--   | $1$ | $1$ | $[1, 7]$ |
--   | $2$ | $2$ | $[2, 4]$ |
--   | $3$ | $2$ | $[4, 7]$ |
--
--   The arcs and their durations are
--   $$t_{d1} = t_{1d} = 1,\quad t_{d2} = t_{2d} = 2,\quad t_{d3} = t_{3d} = 2,\quad t_{12} = t_{21} = 1,\quad t_{13} = t_{31} = 1,\quad t_{23} = 1;$$
--   there is no arc $(3,2)$ and no loop. The costs are left as an arbitrary parameter $c$, since the paper leaves them unspecified ("we are mostly interested in enumerating the feasible solutions in each model").
--
--   **Formalization Note.** The depot is node $0$. Durations of pairs that are not arcs are set to $0$; they never enter a path, which uses arcs only.
-- source:
--   Desrochers, Desrosiers & Solomon, A new optimization algorithm for the vehicle routing problem with time windows, Oper. Res. 40 (1992), pp. 344–345, Sec. 3 and Figure 1

import Mathlib
import Definitions.Def_VRPTWColGen92_Bound_Network

namespace VRPTWColGen92.Bound

/-- The arcs of Figure 1 (p. 345) on the nodes `d = 0, 1, 2, 3`: `(d,1), (1,d), (d,2), (2,d), (d,3),
(3,d), (1,2), (2,1), (1,3), (3,1), (2,3)`; there is no arc `(3,2)`. -/
def fig1Arc (i j : Fin 4) : Prop :=
  (i, j) ∈ ([(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0), (1, 2), (2, 1), (1, 3), (3, 1), (2, 3)] :
    List (Fin 4 × Fin 4))

/-- The arc durations of Figure 1: `t_d1 = t_1d = 1`, `t_d2 = t_2d = 2`, `t_d3 = t_3d = 2`,
`t_12 = t_21 = 1`, `t_13 = t_31 = 1`, `t_23 = 1` (pairs that are not arcs get `0`, never used). -/
def fig1Dur : Fin 4 → Fin 4 → ℝ
  | 0, 1 => 1 | 1, 0 => 1
  | 0, 2 => 2 | 2, 0 => 2
  | 0, 3 => 2 | 3, 0 => 2
  | 1, 2 => 1 | 2, 1 => 1
  | 1, 3 => 1 | 3, 1 => 1
  | 2, 3 => 1
  | _, _ => 0

/-- Demands of Figure 1: `q_d = 0`, `q_1 = 1`, `q_2 = 2`, `q_3 = 2`. -/
def fig1Dem : Fin 4 → ℝ
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 2

/-- Window starts of Figure 1: `a_d = 0`, `a_1 = 1`, `a_2 = 2`, `a_3 = 4`. -/
def fig1A : Fin 4 → ℝ
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4

/-- Window ends of Figure 1: `b_d = 8`, `b_1 = 7`, `b_2 = 4`, `b_3 = 7`. -/
def fig1B : Fin 4 → ℝ
  | 0 => 8 | 1 => 7 | 2 => 4 | 3 => 7

/-- The four-node example of Figure 1, with vehicle capacity `Q = 6` and arbitrary costs `c`
(the paper leaves them unspecified). -/
def fig1 (c : Fin 4 → Fin 4 → ℝ) : Instance 3 where
  arc := fig1Arc
  c := c
  t := fig1Dur
  q := fig1Dem
  a := fig1A
  b := fig1B
  Q := 6

end VRPTWColGen92.Bound


