-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_ellipticY
-- name    : RamanujanNotebooks_shared_ellipticY
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:32:25.962425+00:00
-- url     : https://prove2.me/theorems/ceb54e17-32ab-44b0-9a24-1538a3058706
-- title:
--   Ramanujan's Notebooks, shared: ellipticY
-- statement:
--   Ramanujan's `y = π · _2F_1(1/2, 1/2; 1; 1 - x) / _2F_1(1/2, 1/2; 1; x)` as a function of
--   `x` (Part III, (6.3), p. 101).  With `x = k^2`, `y = π K'/K`.
--
--   Domain: `0 < x < 1` (both series converge, the denominator is `≥ 1`); there `y > 0`, `y`
--   is decreasing, `y(1/2) = π`, and `y(x) y(1 - x) = π^2`.
--   Outside: at `x = 0` and at `x = 1` one of the two series is not summable and Lean returns
--   `y = 0`; classically `y → ∞` as `x → 0` and `y → 0` as `x → 1`.  So the value at `0` is
--   junk and the value at `1` happens to be the limit.  For `x < 0` or `x > 1`: junk.
--   Reference: `y(1/4) = 4.0189187540105703456…`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_ellipticZ

noncomputable section

namespace RamanujanNotebooks

/-- Ramanujan's `y = π · _2F_1(1/2, 1/2; 1; 1 - x) / _2F_1(1/2, 1/2; 1; x)` as a function of
`x` (Part III, (6.3), p. 101).  With `x = k^2`, `y = π K'/K`.

Domain: `0 < x < 1` (both series converge, the denominator is `≥ 1`); there `y > 0`, `y`
is decreasing, `y(1/2) = π`, and `y(x) y(1 - x) = π^2`.
Outside: at `x = 0` and at `x = 1` one of the two series is not summable and Lean returns
`y = 0`; classically `y → ∞` as `x → 0` and `y → 0` as `x → 1`.  So the value at `0` is
junk and the value at `1` happens to be the limit.  For `x < 0` or `x > 1`: junk.
Reference: `y(1/4) = 4.0189187540105703456…`. -/
def ellipticY (x : ℝ) : ℝ :=
  Real.pi * ellipticZ (1 - x) / ellipticZ x

end RamanujanNotebooks

end


