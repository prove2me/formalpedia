-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIV_ch14_phiW
-- name    : RamanujanLostNotebook_PartIV_ch14_phiW
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T15:43:40.4222+00:00
-- url     : https://prove2.me/theorems/f5e0e320-972e-402e-bfd1-0916d1e0e6c2
-- title:
--   Ramanujan's Lost Notebook Part IV, Ch. 14: phiW
-- statement:
--   `φ_w(t) = ∫_0^∞ cos(π t x) / cosh(π x) · e^{-π w x²} dx`, equation (14.1.1) of
--   Andrews–Berndt, Part IV (Ramanujan's integral analogue of a theta function).
--   For `Re w > 0` the integrand has Gaussian decay, so the integral converges absolutely for
--   every complex `t`, and `t ↦ φ_w(t)` is entire.  The definition is only meant for `Re w > 0`.
--   Reference normalisation: `φ_w(i) = 1 / (2 √w)` and `φ_w(w) = e^{-π w / 4} / 2`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 14.

import Mathlib

namespace RamanujanLostNotebook.PartIV

/-- `φ_w(t) = ∫_0^∞ cos(π t x) / cosh(π x) · e^{-π w x²} dx`, equation (14.1.1) of
Andrews–Berndt, Part IV (Ramanujan's integral analogue of a theta function).
For `Re w > 0` the integrand has Gaussian decay, so the integral converges absolutely for
every complex `t`, and `t ↦ φ_w(t)` is entire.  The definition is only meant for `Re w > 0`.
Reference normalisation: `φ_w(i) = 1 / (2 √w)` and `φ_w(w) = e^{-π w / 4} / 2`. -/
noncomputable def phiW (w t : ℂ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ),
    Complex.cos ((Real.pi : ℂ) * t * (x : ℂ)) / Complex.cosh ((Real.pi : ℂ) * (x : ℂ))
      * Complex.exp (-((Real.pi : ℂ) * w * (x : ℂ) ^ 2))

end RamanujanLostNotebook.PartIV


