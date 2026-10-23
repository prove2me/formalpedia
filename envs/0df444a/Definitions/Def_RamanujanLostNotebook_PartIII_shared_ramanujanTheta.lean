-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_shared_ramanujanTheta
-- name    : RamanujanLostNotebook_PartIII_shared_ramanujanTheta
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T02:20:55.120804+00:00
-- url     : https://prove2.me/theorems/4b7df3fc-384d-435a-91c7-d401785fca97
-- title:
--   Ramanujan's Lost Notebook Part III, shared: ramanujanTheta
-- statement:
--   Ramanujan's general theta function `f(a, b) = ∑_{n ∈ ℤ} a^{n(n+1)/2} b^{n(n-1)/2}` for
--   `|ab| < 1` ((2.1.2), p. 9; (8.2.1), p. 220).  For every integer `n` both `n(n+1)/2` and
--   `n(n-1)/2` are nonnegative integers; they are written as `Int.toNat` of the exact integer
--   quotient, so only natural powers of `a` and `b` occur and `a = 0` or `b = 0` is allowed (with
--   Lean's `0 ^ 0 = 1`: `f(a, 0) = 1 + a` and `f(0, b) = 1 + b`).
--
--   Domain: `‖a * b‖ < 1`; the bilateral series converges absolutely there.  The Jacobi triple
--   product `f(a, b) = (-a; ab)_∞ (-b; ab)_∞ (ab; ab)_∞` ((2.1.3), p. 9; (8.2.6), p. 220), the shift
--   rule (2.1.4), p. 10, and the properties (8.2.2)–(8.2.5), p. 220 (`f(a, b) = f(b, a)`,
--   `f(1, a) = 2 f(a, a^3)`, `f(-1, a) = 0`) are theorems about this definition, not part of it.
--   The shift rule contains `(ab)^{-n}`: it holds for `a * b ≠ 0`, and at `a * b = 0`
--   it fails if `0⁻¹` is read as Lean's `0` (for `(a, b, n) = (0, 1/2, 1)` the left side is
--   `3/2`, the right side `0`); the defining series itself allows `a = 0` or `b = 0`.
--   Totalization: for `‖a * b‖ ≥ 1` the terms do not tend to `0` in one direction, the family is
--   not summable, and the value is `0`.
--   The one-argument `f(-q)` of (3.2.3) and (8.2.9) is `eulerF q`, not this function at one
--   argument.
--   Reference: `ramanujanTheta (1/2) (1/5) = 1.7291330641031570156…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- Ramanujan's general theta function `f(a, b) = ∑_{n ∈ ℤ} a^{n(n+1)/2} b^{n(n-1)/2}` for
`|ab| < 1` ((2.1.2), p. 9; (8.2.1), p. 220).  For every integer `n` both `n(n+1)/2` and
`n(n-1)/2` are nonnegative integers; they are written as `Int.toNat` of the exact integer
quotient, so only natural powers of `a` and `b` occur and `a = 0` or `b = 0` is allowed (with
Lean's `0 ^ 0 = 1`: `f(a, 0) = 1 + a` and `f(0, b) = 1 + b`).

Domain: `‖a * b‖ < 1`; the bilateral series converges absolutely there.  The Jacobi triple
product `f(a, b) = (-a; ab)_∞ (-b; ab)_∞ (ab; ab)_∞` ((2.1.3), p. 9; (8.2.6), p. 220), the shift
rule (2.1.4), p. 10, and the properties (8.2.2)–(8.2.5), p. 220 (`f(a, b) = f(b, a)`,
`f(1, a) = 2 f(a, a^3)`, `f(-1, a) = 0`) are theorems about this definition, not part of it.
The shift rule contains `(ab)^{-n}`: it holds for `a * b ≠ 0`, and at `a * b = 0`
it fails if `0⁻¹` is read as Lean's `0` (for `(a, b, n) = (0, 1/2, 1)` the left side is
`3/2`, the right side `0`); the defining series itself allows `a = 0` or `b = 0`.
Totalization: for `‖a * b‖ ≥ 1` the terms do not tend to `0` in one direction, the family is
not summable, and the value is `0`.
The one-argument `f(-q)` of (3.2.3) and (8.2.9) is `eulerF q`, not this function at one
argument.
Reference: `ramanujanTheta (1/2) (1/5) = 1.7291330641031570156…`. -/
def ramanujanTheta (a b : ℂ) : ℂ :=
  ∑' n : ℤ, a ^ (n * (n + 1) / 2).toNat * b ^ (n * (n - 1) / 2).toNat

end RamanujanLostNotebook.PartIII

end


