-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIV_ch17_arctanIntegral
-- name    : RamanujanLostNotebook_PartIV_ch17_arctanIntegral
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T12:27:30.16471+00:00
-- url     : https://prove2.me/theorems/5e445f6b-e0c2-44fe-bd72-be792204e49e
-- title:
--   Ramanujan's Lost Notebook Part IV, Ch. 17: arctanIntegral
-- statement:
--   Ramanujan's inverse tangent integral `Φ(x) = ∫₀ˣ (arctan t)/t dt`, for every real `x`
--   (an odd function; the integrand is bounded, and its junk value at `t = 0` sits on a null set).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 17.

import Mathlib

namespace RamanujanLostNotebook.PartIV

/-- Ramanujan's inverse tangent integral `Φ(x) = ∫₀ˣ (arctan t)/t dt`, for every real `x`
(an odd function; the integrand is bounded, and its junk value at `t = 0` sits on a null set). -/
noncomputable def arctanIntegral (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, Real.arctan t / t

end RamanujanLostNotebook.PartIV


