-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIV_ch04_ramanujanGammaH
-- name    : RamanujanLostNotebook_PartIV_ch04_ramanujanGammaH
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T12:03:03.291842+00:00
-- url     : https://prove2.me/theorems/c5f7e03b-d3c1-47fb-88c0-6cd2701d2fd5
-- title:
--   Ramanujan's Lost Notebook Part IV, Ch. 4: ramanujanGammaH
-- statement:
--   `h(x) = ((e/x)^x Γ(1+x)/√π)^6 - (8x³ + 4x² + x)`, equations (4.5.3)–(4.5.4) of the book;
--   Ramanujan's `θ_x` is `30 * ramanujanGammaH x`. Intended for `x > 0`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 4.

import Mathlib

namespace RamanujanLostNotebook.PartIV

/-- `h(x) = ((e/x)^x Γ(1+x)/√π)^6 - (8x³ + 4x² + x)`, equations (4.5.3)–(4.5.4) of the book;
Ramanujan's `θ_x` is `30 * ramanujanGammaH x`. Intended for `x > 0`. -/
noncomputable def ramanujanGammaH (x : ℝ) : ℝ :=
  ((Real.exp 1 / x) ^ x * Real.Gamma (1 + x) / Real.sqrt Real.pi) ^ (6 : ℕ) -
    (8 * x ^ (3 : ℕ) + 4 * x ^ (2 : ℕ) + x)

end RamanujanLostNotebook.PartIV


