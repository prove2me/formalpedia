-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_rrcfDen
-- name    : RamanujanNotebooks_shared_rrcfDen
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:18:24.398979+00:00
-- url     : https://prove2.me/theorems/fc877f90-8feb-4f47-af98-488462f53049
-- title:
--   Ramanujan's Notebooks, shared: rrcfDen
-- statement:
--   Denominator `B_n` of the `n`-th convergent of
--   `1 + a x / (1 + a x^2 / (1 + ⋯ + a x^n / 1))`: `B_n = B_{n-1} + a x^n B_{n-2}`, `B_0 = 1`,
--   `B_1 = 1`.  The reciprocal continued fraction `1 / (1 + a x / (1 + ⋯ + a x^n / 1))` has
--   numerator `B_n` and denominator `A_n = rrcfNum a x n`.  `B_{n+1}` for the parameter `a`
--   equals `A_n` for the parameter `a x`.
--   A polynomial in `a`, `x`: no domain restriction, no junk value.
--   Reference: `rrcfDen a x 2 = 1 + a x^2`, `rrcfDen 1 x 3 = 1 + x^2 + x^3`;
--   `rrcfDen 1 (1/5) 40 / rrcfNum 1 (1/5) 40 = 0.83866843933274060173…`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib

noncomputable section

namespace RamanujanNotebooks

/-- Denominator `B_n` of the `n`-th convergent of
`1 + a x / (1 + a x^2 / (1 + ⋯ + a x^n / 1))`: `B_n = B_{n-1} + a x^n B_{n-2}`, `B_0 = 1`,
`B_1 = 1`.  The reciprocal continued fraction `1 / (1 + a x / (1 + ⋯ + a x^n / 1))` has
numerator `B_n` and denominator `A_n = rrcfNum a x n`.  `B_{n+1}` for the parameter `a`
equals `A_n` for the parameter `a x`.
A polynomial in `a`, `x`: no domain restriction, no junk value.
Reference: `rrcfDen a x 2 = 1 + a x^2`, `rrcfDen 1 x 3 = 1 + x^2 + x^3`;
`rrcfDen 1 (1/5) 40 / rrcfNum 1 (1/5) 40 = 0.83866843933274060173…`. -/
def rrcfDen (a x : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => 1
  | (n + 2) => rrcfDen a x (n + 1) + a * x ^ (n + 2) * rrcfDen a x n

end RamanujanNotebooks

end


