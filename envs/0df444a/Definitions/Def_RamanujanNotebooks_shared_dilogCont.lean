-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_dilogCont
-- name    : RamanujanNotebooks_shared_dilogCont
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T00:24:42.761238+00:00
-- url     : https://prove2.me/theorems/b19e4a55-2b77-4d7b-96da-bf6ade32983f
-- title:
--   Ramanujan's Notebooks, shared: dilogCont
-- statement:
--   The dilogarithm continued by the integral (6.3), p. 246:
--   `Li_2(z) = -∫_0^z Log(1 - w) / w dw`, the path being the straight segment `w = t z`,
--   `0 ≤ t ≤ 1`, and `Log` the principal branch (`Complex.log`).
--   Domain: every complex `z` not in the real interval `(1, ∞)`; there the integrand is integrable
--   (a removable point at `t = 0`, a logarithmic singularity at `t = 1` when `z = 1`) and the
--   value is the principal branch of `Li_2`, holomorphic on the plane cut along `[1, ∞)`.  For
--   `‖z‖ ≤ 1` it equals the series `∑ z^k/k^2` of (6.1) (the assertion of (6.3); a theorem).
--   Outside: for real `z > 1` the integrand is still integrable and Lean returns the boundary
--   value from below, `Re Li_2(z) - i π log z`; no statement here uses it.
--   Reference: `Li_2(-3) = -1.9393754207667089530…`,
--   `Li_2(2i) = -0.59248494924959145799… + 1.5760154034463234223… i`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib

namespace RamanujanNotebooks

/-- The dilogarithm continued by the integral (6.3), p. 246:
`Li_2(z) = -∫_0^z Log(1 - w) / w dw`, the path being the straight segment `w = t z`,
`0 ≤ t ≤ 1`, and `Log` the principal branch (`Complex.log`).
Domain: every complex `z` not in the real interval `(1, ∞)`; there the integrand is integrable
(a removable point at `t = 0`, a logarithmic singularity at `t = 1` when `z = 1`) and the
value is the principal branch of `Li_2`, holomorphic on the plane cut along `[1, ∞)`.  For
`‖z‖ ≤ 1` it equals the series `∑ z^k/k^2` of (6.1) (the assertion of (6.3); a theorem).
Outside: for real `z > 1` the integrand is still integrable and Lean returns the boundary
value from below, `Re Li_2(z) - i π log z`; no statement here uses it.
Reference: `Li_2(-3) = -1.9393754207667089530…`,
`Li_2(2i) = -0.59248494924959145799… + 1.5760154034463234223… i`. -/
noncomputable def dilogCont (z : ℂ) : ℂ :=
  -∫ t in (0 : ℝ)..1, Complex.log (1 - (t : ℂ) * z) / (t : ℂ)

end RamanujanNotebooks


