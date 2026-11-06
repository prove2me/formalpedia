-- Prove2me | Definitions.Def_ConstrSOSP_boxB
-- name    : ConstrSOSP_boxB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:23.419143+00:00
-- url     : https://prove2.me/theorems/d5073581-6b94-4bfb-a1c2-61674fc7d550
-- title:
--   Right-hand side of the unit square
-- statement:
--   The right-hand side $b=(1,1,0,0)$, so that with $A=[I;-I]$ the constraints read $x_1\le1$, $x_2\le1$, $-x_1\le0$, $-x_2\le0$, i.e. $\mathcal X=[0,1]^2$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Theorem 5.1, p.22

import Mathlib

namespace ConstrSOSP

/-- **Right-hand side of the unit square** `[0, 1]²` (arXiv:2604.02285, 2 Nov 2026, Theorem 5.1,
p.22): `b = (1, 1, 0, 0)`, so that with `boxA = [I; −I]` the constraints read `x₁ ≤ 1`, `x₂ ≤ 1`,
`−x₁ ≤ 0`, `−x₂ ≤ 0`. -/
def boxB : Fin 4 → ℝ :=
  ![1, 1, 0, 0]

end ConstrSOSP


