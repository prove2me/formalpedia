-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch11_ch11H
-- name    : RamanujanLostNotebook_PartV_ch11_ch11H
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T19:16:23.920984+00:00
-- url     : https://prove2.me/theorems/33af5cda-6633-478c-ba79-cc4eb4e938f3
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 11: ch11H
-- statement:
--   The theta series `h(q) = ∑_{n ∈ ℤ} (-1)^n q^{n(5n+3)/2}` of (11.1.2), p. 229 (a function
--   of one variable; not the Lambert-type series `h(x, q)` of (9.6.2) = (11.3.10), which is
--   `tenthH`).  `n(5n+3)` is even and nonnegative for every integer `n`, so the exponent is
--   written as `Int.toNat` of an exact integer quotient.
--
--   Domain: `‖q‖ < 1`; absolutely convergent.  Outside: the family is not summable and the
--   value is `0`.
--   Reference: `1 - q - q^4 + q^7 + q^13 - q^18 - q^27 + …`,
--   `h(1/5) = 0.79841280081893785586…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 11.

import Mathlib

namespace RamanujanLostNotebook.PartV

/-- The theta series `h(q) = ∑_{n ∈ ℤ} (-1)^n q^{n(5n+3)/2}` of (11.1.2), p. 229 (a function
of one variable; not the Lambert-type series `h(x, q)` of (9.6.2) = (11.3.10), which is
`tenthH`).  `n(5n+3)` is even and nonnegative for every integer `n`, so the exponent is
written as `Int.toNat` of an exact integer quotient.

Domain: `‖q‖ < 1`; absolutely convergent.  Outside: the family is not summable and the
value is `0`.
Reference: `1 - q - q^4 + q^7 + q^13 - q^18 - q^27 + …`,
`h(1/5) = 0.79841280081893785586…`. -/
noncomputable def ch11H (q : ℂ) : ℂ :=
  ∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n * (5 * n + 3) / 2).toNat

end RamanujanLostNotebook.PartV


