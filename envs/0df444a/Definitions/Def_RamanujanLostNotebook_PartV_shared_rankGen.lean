-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_rankGen
-- name    : RamanujanLostNotebook_PartV_shared_rankGen
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:06:14.246029+00:00
-- url     : https://prove2.me/theorems/14044176-1c1b-46af-9506-409612d6c0a9
-- title:
--   Ramanujan's Lost Notebook Part V, shared: rankGen
-- statement:
--   Rank generating function
--   `G(z, q) = ∑_{n ≥ 0} q^{n^2} / ((zq; q)_n (q/z; q)_n)` ((4.1.1), p. 35).  The same series
--   is `R(w; q)` of (14.2.3), p. 316, `R_1(z)` of (17.5.1), p. 371, `h_3(x, q)` of (12.5.3),
--   p. 288, and the right side of (19.2.1).
--
--   Domain: `‖q‖ < 1`, `z ≠ 0`, and `z ≠ q^k` for every integer `k ≠ 0` (no vanishing
--   denominator); the series converges absolutely.  There its Taylor coefficients in `q` are
--   `∑_m N(m, n) z^m` (`rankCount`).
--   Outside: `z = 0` gives the junk value `∑ q^{n^2}`; at `z = q^k` the terms with a zero
--   denominator are `0` in Lean, which is not a limit of the function (it has a pole there).
--   Reference: `G(-1, q) = mockF3 q`, `G(i, q) = mockPhi3 q`,
--   `G(3/5 + 4i/5, 1/5) = 1.2520979930474891768…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- Rank generating function
`G(z, q) = ∑_{n ≥ 0} q^{n^2} / ((zq; q)_n (q/z; q)_n)` ((4.1.1), p. 35).  The same series
is `R(w; q)` of (14.2.3), p. 316, `R_1(z)` of (17.5.1), p. 371, `h_3(x, q)` of (12.5.3),
p. 288, and the right side of (19.2.1).

Domain: `‖q‖ < 1`, `z ≠ 0`, and `z ≠ q^k` for every integer `k ≠ 0` (no vanishing
denominator); the series converges absolutely.  There its Taylor coefficients in `q` are
`∑_m N(m, n) z^m` (`rankCount`).
Outside: `z = 0` gives the junk value `∑ q^{n^2}`; at `z = q^k` the terms with a zero
denominator are `0` in Lean, which is not a limit of the function (it has a pole there).
Reference: `G(-1, q) = mockF3 q`, `G(i, q) = mockPhi3 q`,
`G(3/5 + 4i/5, 1/5) = 1.2520979930474891768…`. -/
def rankGen (z q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (n ^ 2) / (qPoch (z * q) q n * qPoch (q / z) q n)

end RamanujanLostNotebook.PartV

end


