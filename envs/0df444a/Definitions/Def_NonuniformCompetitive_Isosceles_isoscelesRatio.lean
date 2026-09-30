-- Prove2me | Definitions.Def_NonuniformCompetitive_Isosceles_isoscelesRatio
-- name    : NonuniformCompetitive_Isosceles_isoscelesRatio
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:54:14.752245+00:00
-- url     : https://prove2.me/theorems/74f52471-b9ad-4786-910d-46e8ed974377
-- title:
--   The ratio $(e_{2d-1}+1/4d)/((e_{2d-1}-1)+1/2d)$ of Theorem 12
-- statement:
--   For a positive integer $d$, let
--   $$e_{2d-1}=\left(1+\frac{1}{2d-1}\right)^{2d-1}=\left(\frac{2d}{2d-1}\right)^{2d-1},$$
--   the number $e_p=(1+1/p)^p$ of the paper at $p=2d-1$, and
--   $$\alpha_d=\frac{e_{2d-1}+\frac{1}{4d}}{\left(e_{2d-1}-1\right)+\frac{1}{2d}}.$$
--   Here $1/4d$ and $1/2d$ mean $1/(4d)$ and $1/(2d)$. This is the optimal randomized competitive ratio of the two-server problem on the isosceles triangle with edge lengths $1,d,d$ (Theorem 12). At $d=1$ (the equilateral triangle) $\alpha_1=3/2$; as $d\to\infty$, $\alpha_d\to e/(e-1)$.
--
--   **Formalization Note** The file defines `eTwoDSubOne d` $=e_{2d-1}$, written as $(2d/(2d-1))^{2d-1}$ with a natural-number exponent, and `isoscelesRatio d` $=\alpha_d$. Both are used only for $d\ge 1$; at $d=0$ they take Lean's junk values ($1$ and $0$).
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, p. 564, Theorem 12 (the ratio); p. 551 (definition of $e_p$); p. 566 ($e_{2d-1}=(2d/(2d-1))^{2d-1}$)

import Mathlib

namespace NonuniformCompetitive.Isosceles

/-- The number `e_{2d-1} = (1 + 1/(2d-1))^(2d-1) = (2d/(2d-1))^(2d-1)` of Karlin, Manasse,
McGeoch and Owicki (Algorithmica 11 (1994), p. 551 defines `e_p = (1 + 1/p)^p`; p. 566 writes
`e_{2d-1}` out as `(2d/(2d-1))^(2d-1)`). The exponent `2 * d - 1` is a natural number; the
definition is only used for `1 ≤ d`, where it is the paper's exponent (at `d = 0` it is the junk
value `1`). -/
noncomputable def eTwoDSubOne (d : ℕ) : ℝ :=
  ((2 * d : ℝ) / (2 * d - 1)) ^ (2 * d - 1)

/-- The optimal randomized competitive ratio of Theorem 12 (p. 564) for the two-server problem
on the isosceles triangle with edge lengths `1, d, d`:
`(e_{2d-1} + 1/(4d)) / ((e_{2d-1} - 1) + 1/(2d))`.
Only meaningful for `1 ≤ d` (at `d = 0` Lean's division by zero gives the junk value `0`). -/
noncomputable def isoscelesRatio (d : ℕ) : ℝ :=
  (eTwoDSubOne d + 1 / (4 * d)) / ((eTwoDSubOne d - 1) + 1 / (2 * d))

end NonuniformCompetitive.Isosceles


