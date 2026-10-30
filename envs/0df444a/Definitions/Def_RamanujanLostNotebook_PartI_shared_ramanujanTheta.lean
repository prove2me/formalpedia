-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_shared_ramanujanTheta
-- name    : RamanujanLostNotebook_PartI_shared_ramanujanTheta
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T02:12:10.803982+00:00
-- url     : https://prove2.me/theorems/18454e48-f10c-47c1-8387-45f95bafc965
-- title:
--   Ramanujan's Lost Notebook Part I, shared: ramanujanTheta
-- statement:
--   Ramanujan's general theta function `f(a, b) = ∑_{n ∈ ℤ} a^{n(n+1)/2} b^{n(n-1)/2}` for
--   `|ab| < 1` ((1.1.5), p. 11).  For every integer `n` both `n(n+1)/2` and `n(n-1)/2` are
--   nonnegative integers; they are written as `Int.toNat` of the exact integer quotient, so only
--   natural powers of `a` and `b` occur and `a = 0` or `b = 0` is allowed (with Lean's
--   `0 ^ 0 = 1`: `f(a, 0) = 1 + a` and `f(0, b) = 1 + b`).
--
--   Domain: `‖a * b‖ < 1`; the bilateral series converges absolutely there.  The Jacobi triple
--   product `f(a, b) = (-a; ab)_∞ (-b; ab)_∞ (ab; ab)_∞` (Lemma 1.2.2, p. 13), `f(-1, a) = 0`
--   ((1.2.4), p. 13), the shift rule
--   `f(a, b) = a^{n(n+1)/2} b^{n(n-1)/2} f(a (ab)^n, b (ab)^{-n})` ((1.2.5), p. 13) and the
--   symmetry `f(a, b) = f(b, a)` are theorems about this definition, not part of it.
--   The shift rule contains `(ab)^{-n}`: it holds for `a * b ≠ 0`, and at `a * b = 0`
--   it fails if `0⁻¹` is read as Lean's `0` (for `(a, b, n) = (0, 1/2, 1)` the left side is
--   `3/2`, the right side `0`); the defining series itself allows `a = 0` or `b = 0`.
--   Totalization: for `‖a * b‖ ≥ 1` the terms do not tend to `0` in one direction, the family is
--   not summable, and the value is `0`.
--   The one-argument `f(-q)` of (1.1.8) is `eulerF q`, not this function at one argument.
--   Reference: `ramanujanTheta (1/2) (1/5) = 1.7291330641031570156…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Ramanujan's general theta function `f(a, b) = ∑_{n ∈ ℤ} a^{n(n+1)/2} b^{n(n-1)/2}` for
`|ab| < 1` ((1.1.5), p. 11).  For every integer `n` both `n(n+1)/2` and `n(n-1)/2` are
nonnegative integers; they are written as `Int.toNat` of the exact integer quotient, so only
natural powers of `a` and `b` occur and `a = 0` or `b = 0` is allowed (with Lean's
`0 ^ 0 = 1`: `f(a, 0) = 1 + a` and `f(0, b) = 1 + b`).

Domain: `‖a * b‖ < 1`; the bilateral series converges absolutely there.  The Jacobi triple
product `f(a, b) = (-a; ab)_∞ (-b; ab)_∞ (ab; ab)_∞` (Lemma 1.2.2, p. 13), `f(-1, a) = 0`
((1.2.4), p. 13), the shift rule
`f(a, b) = a^{n(n+1)/2} b^{n(n-1)/2} f(a (ab)^n, b (ab)^{-n})` ((1.2.5), p. 13) and the
symmetry `f(a, b) = f(b, a)` are theorems about this definition, not part of it.
The shift rule contains `(ab)^{-n}`: it holds for `a * b ≠ 0`, and at `a * b = 0`
it fails if `0⁻¹` is read as Lean's `0` (for `(a, b, n) = (0, 1/2, 1)` the left side is
`3/2`, the right side `0`); the defining series itself allows `a = 0` or `b = 0`.
Totalization: for `‖a * b‖ ≥ 1` the terms do not tend to `0` in one direction, the family is
not summable, and the value is `0`.
The one-argument `f(-q)` of (1.1.8) is `eulerF q`, not this function at one argument.
Reference: `ramanujanTheta (1/2) (1/5) = 1.7291330641031570156…`. -/
def ramanujanTheta (a b : ℂ) : ℂ :=
  ∑' n : ℤ, a ^ (n * (n + 1) / 2).toNat * b ^ (n * (n - 1) / 2).toNat

end RamanujanLostNotebook.PartI

end


