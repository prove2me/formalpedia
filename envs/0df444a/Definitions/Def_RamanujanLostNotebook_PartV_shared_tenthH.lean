-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_tenthH
-- name    : RamanujanLostNotebook_PartV_shared_tenthH
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T17:12:33.648214+00:00
-- url     : https://prove2.me/theorems/bc5386f8-cfed-4db3-ac76-b2d85d43c07f
-- title:
--   Ramanujan's Lost Notebook Part V, shared: tenthH
-- statement:
--   The Lambert-type series `h(x, q)` of (9.6.2), p. 195 (recalled as (11.3.10), p. 235;
--   Chapter 10 uses its own analogue `k(x, q)` of (10.6.2)):
--   `h(x, q) = φ(-q)^{-1} ∑_{n ∈ ℤ} (-1)^n q^{n(n+1)} / (1 - q^n x)`.
--   `n(n+1) ≥ 0` is written with `Int.toNat`; `q ^ n` is an integer power.
--
--   Domain: `0 < ‖q‖ < 1`, and `x ≠ q^k` for every integer `k` (no vanishing denominator);
--   absolutely convergent.  Outside: junk.
--   Reference: `h(1/2, 1/5) = 4.3415363887206243464…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_thetaPhi

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- The Lambert-type series `h(x, q)` of (9.6.2), p. 195 (recalled as (11.3.10), p. 235;
Chapter 10 uses its own analogue `k(x, q)` of (10.6.2)):
`h(x, q) = φ(-q)^{-1} ∑_{n ∈ ℤ} (-1)^n q^{n(n+1)} / (1 - q^n x)`.
`n(n+1) ≥ 0` is written with `Int.toNat`; `q ^ n` is an integer power.

Domain: `0 < ‖q‖ < 1`, and `x ≠ q^k` for every integer `k` (no vanishing denominator);
absolutely convergent.  Outside: junk.
Reference: `h(1/2, 1/5) = 4.3415363887206243464…`. -/
def tenthH (x q : ℂ) : ℂ :=
  1 / thetaPhi (-q) * ∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n * (n + 1)).toNat / (1 - q ^ n * x)

end RamanujanLostNotebook.PartV

end


