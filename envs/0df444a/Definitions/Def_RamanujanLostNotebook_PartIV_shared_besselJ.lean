-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIV_shared_besselJ
-- name    : RamanujanLostNotebook_PartIV_shared_besselJ
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T14:56:43.074126+00:00
-- url     : https://prove2.me/theorems/b8da4f46-f90c-4507-bafa-b89c5e6c0f6a
-- title:
--   Ramanujan's Lost Notebook Part IV, shared: besselJ
-- statement:
--   Bessel function of the first kind `J_ν(x)` for real order `ν` and real argument `x`
--   (DLMF 10.2.2; (2.1.1) of the book):
--   `J_ν(x) = ∑_{m ≥ 0} (-1)^m / (m! Γ(ν + m + 1)) · (x/2)^(ν + 2m)`.
--
--   The reciprocal Gamma factor is written `(Real.Gamma _)⁻¹`.  Mathlib sets `Real.Gamma` to
--   `0` at `0, -1, -2, …`, so the factor is `0` exactly where the entire function `1/Γ`
--   vanishes; for `ν = -n` a negative integer the terms `m < n` drop out and the series gives
--   the correct value `J_{-n}(x) = (-1)^n J_n(x)`.
--
--   Domain: for `0 < x` the series converges absolutely for every real `ν` and equals `J_ν(x)`.
--   Outside the source domain, the series still converges absolutely (the power is `Real.rpow`).
--   At `x = 0` Lean returns `1` when `ν = 0` and `0` when `ν ≠ 0`; for negative
--   noninteger order this is only totalized output, while at negative integer
--   order it agrees with the zero-valued continuous extension.  For `x < 0`,
--   `Real.rpow` gives `besselJ ν x = cos (Real.pi * ν) * besselJ ν (-x)`.
--   This is the standard integer-order extension and, at noninteger order, the
--   real part of the principal complex branch rather than a standard
--   real-domain value.  Use `0 < x` for source-faithful statements.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013.

import Mathlib

namespace RamanujanLostNotebook.PartIV

/-- Bessel function of the first kind `J_ν(x)` for real order `ν` and real argument `x`
(DLMF 10.2.2; (2.1.1) of the book):
`J_ν(x) = ∑_{m ≥ 0} (-1)^m / (m! Γ(ν + m + 1)) · (x/2)^(ν + 2m)`.

The reciprocal Gamma factor is written `(Real.Gamma _)⁻¹`.  Mathlib sets `Real.Gamma` to
`0` at `0, -1, -2, …`, so the factor is `0` exactly where the entire function `1/Γ`
vanishes; for `ν = -n` a negative integer the terms `m < n` drop out and the series gives
the correct value `J_{-n}(x) = (-1)^n J_n(x)`.

Domain: for `0 < x` the series converges absolutely for every real `ν` and equals `J_ν(x)`.
Outside the source domain, the series still converges absolutely (the power is `Real.rpow`).
At `x = 0` Lean returns `1` when `ν = 0` and `0` when `ν ≠ 0`; for negative
noninteger order this is only totalized output, while at negative integer
order it agrees with the zero-valued continuous extension.  For `x < 0`,
`Real.rpow` gives `besselJ ν x = cos (Real.pi * ν) * besselJ ν (-x)`.
This is the standard integer-order extension and, at noninteger order, the
real part of the principal complex branch rather than a standard
real-domain value.  Use `0 < x` for source-faithful statements. -/
noncomputable def besselJ (ν x : ℝ) : ℝ :=
  ∑' m : ℕ, (-1 : ℝ) ^ m / (m.factorial : ℝ) * (Real.Gamma (ν + (m : ℝ) + 1))⁻¹
    * (x / 2) ^ (ν + 2 * (m : ℝ))

end RamanujanLostNotebook.PartIV


