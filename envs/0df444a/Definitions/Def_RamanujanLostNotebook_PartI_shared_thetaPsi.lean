-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_shared_thetaPsi
-- name    : RamanujanLostNotebook_PartI_shared_thetaPsi
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T02:12:14.520648+00:00
-- url     : https://prove2.me/theorems/242d9070-adc3-4c80-b26e-18e9a2554235
-- title:
--   Ramanujan's Lost Notebook Part I, shared: thetaPsi
-- statement:
--   Ramanujan's `ψ(q) = f(q, q^3) = ∑_{n ≥ 0} q^{n(n+1)/2}` ((1.1.7), p. 11).  The exponent
--   `n * (n + 1) / 2` is exact natural-number division, since `n(n+1)` is even.
--
--   Domain: `‖q‖ < 1`, where the series converges absolutely.  The product form
--   `ψ(q) = (q^2; q^2)_∞ / (q; q^2)_∞` printed in (1.1.7) and the equality
--   `thetaPsi q = ramanujanTheta q (q ^ 3)` are theorems.
--   Totalization: for `‖q‖ ≥ 1` the terms do not tend to `0` and the value is `0`;
--   `thetaPsi 0 = 1`.
--   Reference: Taylor expansion `1 + q + q^3 + q^6 + q^10 + q^15 + …`;
--   `thetaPsi (1/5) = 1.2080641024327700971…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Ramanujan's `ψ(q) = f(q, q^3) = ∑_{n ≥ 0} q^{n(n+1)/2}` ((1.1.7), p. 11).  The exponent
`n * (n + 1) / 2` is exact natural-number division, since `n(n+1)` is even.

Domain: `‖q‖ < 1`, where the series converges absolutely.  The product form
`ψ(q) = (q^2; q^2)_∞ / (q; q^2)_∞` printed in (1.1.7) and the equality
`thetaPsi q = ramanujanTheta q (q ^ 3)` are theorems.
Totalization: for `‖q‖ ≥ 1` the terms do not tend to `0` and the value is `0`;
`thetaPsi 0 = 1`.
Reference: Taylor expansion `1 + q + q^3 + q^6 + q^10 + q^15 + …`;
`thetaPsi (1/5) = 1.2080641024327700971…`. -/
def thetaPsi (q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (n * (n + 1) / 2)

end RamanujanLostNotebook.PartI

end


