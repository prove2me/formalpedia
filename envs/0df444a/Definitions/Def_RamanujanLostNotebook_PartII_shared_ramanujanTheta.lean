-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_shared_ramanujanTheta
-- name    : RamanujanLostNotebook_PartII_shared_ramanujanTheta
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T02:16:57.76199+00:00
-- url     : https://prove2.me/theorems/855cf8c4-58cd-4a6a-8c6b-7294c519bd8a
-- title:
--   Ramanujan's Lost Notebook Part II, shared: ramanujanTheta
-- statement:
--   Ramanujan's general theta function `f(a, b) = ∑_{n ∈ ℤ} a^{n(n+1)/2} b^{n(n-1)/2}` for
--   `|ab| < 1` ((1.4.8), p. 17; restated on p. 173).  For every integer `n` both `n(n+1)/2` and
--   `n(n-1)/2` are nonnegative integers; they are written as `Int.toNat` of the exact integer
--   quotient, so only natural powers of `a` and `b` occur and `a = 0` or `b = 0` is allowed (with
--   Lean's `0 ^ 0 = 1`: `f(a, 0) = 1 + a` and `f(0, b) = 1 + b`).
--
--   Domain: `‖a * b‖ < 1`; the bilateral series converges absolutely there.  The Jacobi triple
--   product `f(a, b) = (-a; ab)_∞ (-b; ab)_∞ (ab; ab)_∞` (printed together with the definition in
--   (1.4.8), and as Theorem 8.1.1, (8.1.1), p. 174), `f(-1, a) = 0` ((1.4.12), p. 18) and the
--   shift rule (1.4.13), p. 18, are theorems about this definition, not part of it.
--   The shift rule contains `(ab)^{-n}`: it holds for `a * b ≠ 0`, and at `a * b = 0`
--   it fails if `0⁻¹` is read as Lean's `0` (for `(a, b, n) = (0, 1/2, 1)` the left side is
--   `3/2`, the right side `0`); the defining series itself allows `a = 0` or `b = 0`.
--   Totalization: for `‖a * b‖ ≥ 1` the terms do not tend to `0` in one direction, the family is
--   not summable, and the value is `0`.
--   The one-argument `f(-q)` of (1.4.11) is `eulerF q`, not this function at one argument.
--   Reference: `ramanujanTheta (1/2) (1/5) = 1.7291330641031570156…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Ramanujan's general theta function `f(a, b) = ∑_{n ∈ ℤ} a^{n(n+1)/2} b^{n(n-1)/2}` for
`|ab| < 1` ((1.4.8), p. 17; restated on p. 173).  For every integer `n` both `n(n+1)/2` and
`n(n-1)/2` are nonnegative integers; they are written as `Int.toNat` of the exact integer
quotient, so only natural powers of `a` and `b` occur and `a = 0` or `b = 0` is allowed (with
Lean's `0 ^ 0 = 1`: `f(a, 0) = 1 + a` and `f(0, b) = 1 + b`).

Domain: `‖a * b‖ < 1`; the bilateral series converges absolutely there.  The Jacobi triple
product `f(a, b) = (-a; ab)_∞ (-b; ab)_∞ (ab; ab)_∞` (printed together with the definition in
(1.4.8), and as Theorem 8.1.1, (8.1.1), p. 174), `f(-1, a) = 0` ((1.4.12), p. 18) and the
shift rule (1.4.13), p. 18, are theorems about this definition, not part of it.
The shift rule contains `(ab)^{-n}`: it holds for `a * b ≠ 0`, and at `a * b = 0`
it fails if `0⁻¹` is read as Lean's `0` (for `(a, b, n) = (0, 1/2, 1)` the left side is
`3/2`, the right side `0`); the defining series itself allows `a = 0` or `b = 0`.
Totalization: for `‖a * b‖ ≥ 1` the terms do not tend to `0` in one direction, the family is
not summable, and the value is `0`.
The one-argument `f(-q)` of (1.4.11) is `eulerF q`, not this function at one argument.
Reference: `ramanujanTheta (1/2) (1/5) = 1.7291330641031570156…`. -/
def ramanujanTheta (a b : ℂ) : ℂ :=
  ∑' n : ℤ, a ^ (n * (n + 1) / 2).toNat * b ^ (n * (n - 1) / 2).toNat

end RamanujanLostNotebook.PartII

end


