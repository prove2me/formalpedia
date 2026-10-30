-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_tenthK
-- name    : RamanujanLostNotebook_PartV_shared_tenthK
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T18:15:36.642222+00:00
-- url     : https://prove2.me/theorems/13f861ec-f203-4fb5-8fde-464772e01148
-- title:
--   Ramanujan's Lost Notebook Part V, shared: tenthK
-- statement:
--   The Lambert-type series `k(x, q)` of (10.6.2), p. 216, recalled as (11.3.18), p. 236 (the
--   two displays are the same expression; Chapter 11 writes the factors as `x ψ(q)` and
--   `x^2 q^{2n}`):
--   `k(x, q) = (ψ(q) x)^{-1} ∑_{n ∈ ℤ} q^{n(2n+1)} / (1 - q^{2n} x^2)`.
--   `n(2n+1) ≥ 0` is written with `Int.toNat`; `q ^ (2n)` is an integer power.  The analogue of,
--   and a different function from, `h(x, q)` of (9.6.2).
--
--   Domain: `0 < ‖q‖ < 1`, `x ≠ 0`, and `x^2 ≠ q^(2k)` for every integer `k` (no vanishing
--   denominator); absolutely convergent.  Outside: junk.
--   Reference: `k(1/3, 1/5) = 2.5343064484339244890…`,
--   `k(1/2, 1/5) = 2.1576977428547986159…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_thetaPsi

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- The Lambert-type series `k(x, q)` of (10.6.2), p. 216, recalled as (11.3.18), p. 236 (the
two displays are the same expression; Chapter 11 writes the factors as `x ψ(q)` and
`x^2 q^{2n}`):
`k(x, q) = (ψ(q) x)^{-1} ∑_{n ∈ ℤ} q^{n(2n+1)} / (1 - q^{2n} x^2)`.
`n(2n+1) ≥ 0` is written with `Int.toNat`; `q ^ (2n)` is an integer power.  The analogue of,
and a different function from, `h(x, q)` of (9.6.2).

Domain: `0 < ‖q‖ < 1`, `x ≠ 0`, and `x^2 ≠ q^(2k)` for every integer `k` (no vanishing
denominator); absolutely convergent.  Outside: junk.
Reference: `k(1/3, 1/5) = 2.5343064484339244890…`,
`k(1/2, 1/5) = 2.1576977428547986159…`. -/
def tenthK (x q : ℂ) : ℂ :=
  1 / (thetaPsi q * x) * ∑' n : ℤ, q ^ (n * (2 * n + 1)).toNat / (1 - q ^ (2 * n) * x ^ 2)

end RamanujanLostNotebook.PartV

end


