-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIV_shared_besselKC
-- name    : RamanujanLostNotebook_PartIV_shared_besselKC
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T14:56:43.23498+00:00
-- url     : https://prove2.me/theorems/5b5c8bc0-6c35-4cf8-9b72-e80278d55e89
-- title:
--   Ramanujan's Lost Notebook Part IV, shared: besselKC
-- statement:
--   Modified Bessel function of the second kind `K_ν(z)` for complex order `ν` and complex
--   argument `z` in the open right half-plane (DLMF 10.32.9, valid for `|arg z| < π/2`):
--   `K_ν(z) = ∫_0^∞ exp (-z cosh t) cosh (ν t) dt`.
--
--   For real `ν` and real `x > 0` it is the complex number `(besselK ν x : ℂ)`.
--
--   Domain: for `0 < z.re` the integrand is bounded in absolute value by
--   `exp (-z.re cosh t) cosh (ν.re t)`, the integral converges absolutely for every complex
--   `ν`, and the value is the principal `K_ν(z)`.
--   Outside it: for `z.re ≤ 0` the integrand is not integrable and Lean's Bochner integral
--   gives the junk value `0`.  (The classical `K_ν` continues analytically to `z.re ≤ 0`,
--   `z ≠ 0`; this definition does NOT represent it there.)
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013.

import Mathlib

namespace RamanujanLostNotebook.PartIV

/-- Modified Bessel function of the second kind `K_ν(z)` for complex order `ν` and complex
argument `z` in the open right half-plane (DLMF 10.32.9, valid for `|arg z| < π/2`):
`K_ν(z) = ∫_0^∞ exp (-z cosh t) cosh (ν t) dt`.

For real `ν` and real `x > 0` it is the complex number `(besselK ν x : ℂ)`.

Domain: for `0 < z.re` the integrand is bounded in absolute value by
`exp (-z.re cosh t) cosh (ν.re t)`, the integral converges absolutely for every complex
`ν`, and the value is the principal `K_ν(z)`.
Outside it: for `z.re ≤ 0` the integrand is not integrable and Lean's Bochner integral
gives the junk value `0`.  (The classical `K_ν` continues analytically to `z.re ≤ 0`,
`z ≠ 0`; this definition does NOT represent it there.) -/
noncomputable def besselKC (ν z : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ),
    Complex.exp (-(z * Complex.cosh (t : ℂ))) * Complex.cosh (ν * (t : ℂ))

end RamanujanLostNotebook.PartIV


