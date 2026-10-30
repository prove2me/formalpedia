-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch16_rrcfNum
-- name    : RamanujanLostNotebook_PartV_ch16_rrcfNum
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T19:01:57.384648+00:00
-- url     : https://prove2.me/theorems/06c73c24-aba6-49b3-b1a7-99d5e0456128
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 16: rrcfNum
-- statement:
--   Numerator `A_n` of the `n`-th convergent of the finite Rogers–Ramanujan continued fraction
--   `1 + a x / (1 + a x^2 / (1 + ⋯ + a x^n / 1))`, defined by the standard three-term recurrence
--   (p. 359) `A_n = A_{n-1} + a x^n A_{n-2}`, `A_0 = 1`, `A_1 = 1 + a x`.
--   It is the book's `P_n(a)` of (16.2.8), p. 360.  With `B_n` the denominator given by the same
--   recurrence started at `B_0 = B_1 = 1`, the value of the finite continued fraction is
--   `A_n / B_n` whenever no denominator met in evaluating it vanishes, and "the continued
--   fraction is `0`" means `A_n = 0 ∧ B_n ≠ 0`.
--   A polynomial in `a`, `x`: no domain restriction, no junk value.
--   Reference: `rrcfNum a x 2 = 1 + a x + a x^2`, `rrcfNum 1 x 3 = 1 + x + x^2 + x^3 + x^4`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 16.

import Mathlib

namespace RamanujanLostNotebook.PartV

/-- Numerator `A_n` of the `n`-th convergent of the finite Rogers–Ramanujan continued fraction
`1 + a x / (1 + a x^2 / (1 + ⋯ + a x^n / 1))`, defined by the standard three-term recurrence
(p. 359) `A_n = A_{n-1} + a x^n A_{n-2}`, `A_0 = 1`, `A_1 = 1 + a x`.
It is the book's `P_n(a)` of (16.2.8), p. 360.  With `B_n` the denominator given by the same
recurrence started at `B_0 = B_1 = 1`, the value of the finite continued fraction is
`A_n / B_n` whenever no denominator met in evaluating it vanishes, and "the continued
fraction is `0`" means `A_n = 0 ∧ B_n ≠ 0`.
A polynomial in `a`, `x`: no domain restriction, no junk value.
Reference: `rrcfNum a x 2 = 1 + a x + a x^2`, `rrcfNum 1 x 3 = 1 + x + x^2 + x^3 + x^4`. -/
noncomputable def rrcfNum (a x : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => 1 + a * x
  | (n + 2) => rrcfNum a x (n + 1) + a * x ^ (n + 2) * rrcfNum a x n

end RamanujanLostNotebook.PartV


