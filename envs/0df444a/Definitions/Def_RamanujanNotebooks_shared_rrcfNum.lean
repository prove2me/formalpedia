-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_rrcfNum
-- name    : RamanujanNotebooks_shared_rrcfNum
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:18:22.697608+00:00
-- url     : https://prove2.me/theorems/eee4d00b-cad5-4316-85a7-285308f43bb7
-- title:
--   Ramanujan's Notebooks, shared: rrcfNum
-- statement:
--   Numerator `A_n` of the `n`-th convergent of the finite continued fraction
--   `1 + a x / (1 + a x^2 / (1 + ⋯ + a x^n / 1))`, by the three-term recurrence
--   `A_n = A_{n-1} + a x^n A_{n-2}`, `A_0 = 1`, `A_1 = 1 + a x`.  With `B_n = rrcfDen a x n`,
--   the value of the finite continued fraction is `A_n / B_n` whenever no denominator met in
--   evaluating it vanishes.
--
--   The Rogers–Ramanujan continued fraction of Entry 38(iii) (Part III, p. 79),
--   `1 / (1 + q / (1 + q^2 / (1 + ⋯)))`, is the limit of `rrcfDen 1 q n / rrcfNum 1 q n`; for
--   `‖q‖ < 1` this limit is `f(-q, -q^4) / f(-q^2, -q^3)`.  Berndt's `R(q)` (Part V, p. 9) is
--   `q^{1/5}` times it, and `S(q) = -R(-q)`.
--   A polynomial in `a`, `x`: no domain restriction, no junk value.
--   Reference: `rrcfNum a x 2 = 1 + a x + a x^2`, `rrcfNum 1 x 3 = 1 + x + x^2 + x^3 + x^4`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib

noncomputable section

namespace RamanujanNotebooks

/-- Numerator `A_n` of the `n`-th convergent of the finite continued fraction
`1 + a x / (1 + a x^2 / (1 + ⋯ + a x^n / 1))`, by the three-term recurrence
`A_n = A_{n-1} + a x^n A_{n-2}`, `A_0 = 1`, `A_1 = 1 + a x`.  With `B_n = rrcfDen a x n`,
the value of the finite continued fraction is `A_n / B_n` whenever no denominator met in
evaluating it vanishes.

The Rogers–Ramanujan continued fraction of Entry 38(iii) (Part III, p. 79),
`1 / (1 + q / (1 + q^2 / (1 + ⋯)))`, is the limit of `rrcfDen 1 q n / rrcfNum 1 q n`; for
`‖q‖ < 1` this limit is `f(-q, -q^4) / f(-q^2, -q^3)`.  Berndt's `R(q)` (Part V, p. 9) is
`q^{1/5}` times it, and `S(q) = -R(-q)`.
A polynomial in `a`, `x`: no domain restriction, no junk value.
Reference: `rrcfNum a x 2 = 1 + a x + a x^2`, `rrcfNum 1 x 3 = 1 + x + x^2 + x^3 + x^4`. -/
def rrcfNum (a x : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => 1 + a * x
  | (n + 2) => rrcfNum a x (n + 1) + a * x ^ (n + 2) * rrcfNum a x n

end RamanujanNotebooks

end


