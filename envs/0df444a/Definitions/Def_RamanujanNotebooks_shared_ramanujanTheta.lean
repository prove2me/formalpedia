-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_ramanujanTheta
-- name    : RamanujanNotebooks_shared_ramanujanTheta
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:18:14.443714+00:00
-- url     : https://prove2.me/theorems/eea833d0-d3db-4a8c-91da-e19ba028de84
-- title:
--   Ramanujan's Notebooks, shared: ramanujanTheta
-- statement:
--   Ramanujan's general theta function
--   `f(a, b) = ∑_{k ∈ ℤ} a^{k(k+1)/2} b^{k(k-1)/2}` ((18.1), Part III, p. 34).  Both exponents
--   are nonnegative integers for every integer index; they are written with `Int.toNat`, so no
--   inverse of `a` or `b` occurs.
--
--   Domain: `‖a * b‖ < 1`; the series converges absolutely.  There the Jacobi triple product
--   `f(a, b) = (-a; ab)_∞ (-b; ab)_∞ (ab; ab)_∞` holds (Entry 19; a theorem, not part of the
--   definition).  `a = 0` or `b = 0` is allowed: `f(0, b) = 1 + b`.
--   Outside: for `‖a * b‖ ≥ 1` the family is not summable and the value is `0`.
--   Reference: `f(1/2, 1/5) = 1.7291330641031570156…`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib

noncomputable section

namespace RamanujanNotebooks

/-- Ramanujan's general theta function
`f(a, b) = ∑_{k ∈ ℤ} a^{k(k+1)/2} b^{k(k-1)/2}` ((18.1), Part III, p. 34).  Both exponents
are nonnegative integers for every integer index; they are written with `Int.toNat`, so no
inverse of `a` or `b` occurs.

Domain: `‖a * b‖ < 1`; the series converges absolutely.  There the Jacobi triple product
`f(a, b) = (-a; ab)_∞ (-b; ab)_∞ (ab; ab)_∞` holds (Entry 19; a theorem, not part of the
definition).  `a = 0` or `b = 0` is allowed: `f(0, b) = 1 + b`.
Outside: for `‖a * b‖ ≥ 1` the family is not summable and the value is `0`.
Reference: `f(1/2, 1/5) = 1.7291330641031570156…`. -/
def ramanujanTheta (a b : ℂ) : ℂ :=
  ∑' n : ℤ, a ^ (n * (n + 1) / 2).toNat * b ^ (n * (n - 1) / 2).toNat

end RamanujanNotebooks

end


