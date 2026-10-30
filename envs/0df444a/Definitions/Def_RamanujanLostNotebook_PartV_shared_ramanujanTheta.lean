-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_ramanujanTheta
-- name    : RamanujanLostNotebook_PartV_shared_ramanujanTheta
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:05:56.01407+00:00
-- url     : https://prove2.me/theorems/40f86948-1a98-4ba2-b08c-fdd0e5680944
-- title:
--   Ramanujan's Lost Notebook Part V, shared: ramanujanTheta
-- statement:
--   Ramanujan's general theta function
--   `f(a, b) = ∑_{n ∈ ℤ} a^{n(n+1)/2} b^{n(n-1)/2}` ((4.4.1), p. 44; (5.1.1), p. 59; (6.3.1),
--   (9.2.1), (12.1.5)).  Both exponents are nonnegative integers for every `n ∈ ℤ`; they are
--   written with `Int.toNat`, so no inverse of `a` or `b` occurs.
--
--   Domain: `‖a * b‖ < 1`; the series converges absolutely.  There the Jacobi triple product
--   `f(a, b) = (-a; ab)_∞ (-b; ab)_∞ (ab; ab)_∞` holds (a theorem, not part of the definition).
--   `a = 0` or `b = 0` is allowed: `f(0, b) = 1 + b`.
--   Outside: for `‖a * b‖ ≥ 1` the family is not summable and the value is `0`.
--   Reference: `f(1/2, 1/5) = 1.7291330641031570156…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- Ramanujan's general theta function
`f(a, b) = ∑_{n ∈ ℤ} a^{n(n+1)/2} b^{n(n-1)/2}` ((4.4.1), p. 44; (5.1.1), p. 59; (6.3.1),
(9.2.1), (12.1.5)).  Both exponents are nonnegative integers for every `n ∈ ℤ`; they are
written with `Int.toNat`, so no inverse of `a` or `b` occurs.

Domain: `‖a * b‖ < 1`; the series converges absolutely.  There the Jacobi triple product
`f(a, b) = (-a; ab)_∞ (-b; ab)_∞ (ab; ab)_∞` holds (a theorem, not part of the definition).
`a = 0` or `b = 0` is allowed: `f(0, b) = 1 + b`.
Outside: for `‖a * b‖ ≥ 1` the family is not summable and the value is `0`.
Reference: `f(1/2, 1/5) = 1.7291330641031570156…`. -/
def ramanujanTheta (a b : ℂ) : ℂ :=
  ∑' n : ℤ, a ^ (n * (n + 1) / 2).toNat * b ^ (n * (n - 1) / 2).toNat

end RamanujanLostNotebook.PartV

end


