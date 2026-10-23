-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIV_ch13_digammaRemainder
-- name    : RamanujanLostNotebook_PartIV_ch13_digammaRemainder
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T15:14:39.339398+00:00
-- url     : https://prove2.me/theorems/e3f34c69-5d29-4cae-949b-954a52ad7380
-- title:
--   Ramanujan's Lost Notebook Part IV, Ch. 13: digammaRemainder
-- statement:
--   The function `φ(x) = ψ(x) + 1/(2x) - log x` of equation (13.3.2), where `ψ = Γ'/Γ` is
--   the digamma function (`logDeriv Real.Gamma`).  For `x → +∞` it is `-1/(12 x²) + O(1/x⁴)`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 13.

import Mathlib

namespace RamanujanLostNotebook.PartIV

/-- The function `φ(x) = ψ(x) + 1/(2x) - log x` of equation (13.3.2), where `ψ = Γ'/Γ` is
the digamma function (`logDeriv Real.Gamma`).  For `x → +∞` it is `-1/(12 x²) + O(1/x⁴)`. -/
noncomputable def digammaRemainder (x : ℝ) : ℝ :=
  logDeriv Real.Gamma x + 1 / (2 * x) - Real.log x

end RamanujanLostNotebook.PartIV


