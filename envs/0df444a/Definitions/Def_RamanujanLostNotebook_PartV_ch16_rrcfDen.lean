-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch16_rrcfDen
-- name    : RamanujanLostNotebook_PartV_ch16_rrcfDen
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T19:01:59.447736+00:00
-- url     : https://prove2.me/theorems/725c4517-8a71-4517-91e3-fe6d10228d25
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 16: rrcfDen
-- statement:
--   Denominator `B_n` of the `n`-th convergent of
--   `1 + a x / (1 + a x^2 / (1 + ⋯ + a x^n / 1))`: `B_n = B_{n-1} + a x^n B_{n-2}`, `B_0 = 1`,
--   `B_1 = 1` (p. 359); the book's `Q_n(a)` of (16.2.8).  The reciprocal continued fraction
--   `1 / (1 + a x / (1 + ⋯ + a x^n / 1))` has numerator `B_n` and denominator `A_n` (the
--   numerator of the convergent, given by the same recurrence started at `A_0 = 1`,
--   `A_1 = 1 + a x`).  `B_{n+1}` for the parameter `a` equals `A_n` for the parameter `a x`.
--   A polynomial in `a`, `x`: no domain restriction, no junk value.
--   Reference: `rrcfDen a x 2 = 1 + a x^2`, `rrcfDen 1 x 3 = 1 + x^2 + x^3`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 16.

import Mathlib

namespace RamanujanLostNotebook.PartV

/-- Denominator `B_n` of the `n`-th convergent of
`1 + a x / (1 + a x^2 / (1 + ⋯ + a x^n / 1))`: `B_n = B_{n-1} + a x^n B_{n-2}`, `B_0 = 1`,
`B_1 = 1` (p. 359); the book's `Q_n(a)` of (16.2.8).  The reciprocal continued fraction
`1 / (1 + a x / (1 + ⋯ + a x^n / 1))` has numerator `B_n` and denominator `A_n` (the
numerator of the convergent, given by the same recurrence started at `A_0 = 1`,
`A_1 = 1 + a x`).  `B_{n+1}` for the parameter `a` equals `A_n` for the parameter `a x`.
A polynomial in `a`, `x`: no domain restriction, no junk value.
Reference: `rrcfDen a x 2 = 1 + a x^2`, `rrcfDen 1 x 3 = 1 + x^2 + x^3`. -/
noncomputable def rrcfDen (a x : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => 1
  | (n + 2) => rrcfDen a x (n + 1) + a * x ^ (n + 2) * rrcfDen a x n

end RamanujanLostNotebook.PartV


