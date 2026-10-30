-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch18_ch18GammaH
-- name    : RamanujanLostNotebook_PartV_ch18_ch18GammaH
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T21:59:46.125593+00:00
-- url     : https://prove2.me/theorems/e6552762-02ed-4573-b8af-fcb8cfc7cfa1
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 18: ch18GammaH
-- statement:
--   `h(x) = ((e/x)^x Γ(1+x)/√π)^6 - (8x³ + 4x² + x)`, (4.5.3)–(4.5.4) of Part IV.  The body
--   is identical to `RamanujanLostNotebook.PartIV.ramanujanGammaH` (Part IV, Chapter 4,
--   `Defs.lean`).  Ramanujan's `θ_x` is `30 * ch18GammaH x`; for a positive integer `n` this is the
--   `θ_n` of Theorem 18.4.1, because `Γ(1+n) = n!`.  Intended for `x > 0`.
--   Reference: `30 h(1) = 0.33592874025…`, `30 h(2) = 0.51176232103…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 18.

import Mathlib

namespace RamanujanLostNotebook.PartV

/-- `h(x) = ((e/x)^x Γ(1+x)/√π)^6 - (8x³ + 4x² + x)`, (4.5.3)–(4.5.4) of Part IV.  The body
is identical to `RamanujanLostNotebook.PartIV.ramanujanGammaH` (Part IV, Chapter 4,
`Defs.lean`).  Ramanujan's `θ_x` is `30 * ch18GammaH x`; for a positive integer `n` this is the
`θ_n` of Theorem 18.4.1, because `Γ(1+n) = n!`.  Intended for `x > 0`.
Reference: `30 h(1) = 0.33592874025…`, `30 h(2) = 0.51176232103…`. -/
noncomputable def ch18GammaH (x : ℝ) : ℝ :=
  ((Real.exp 1 / x) ^ x * Real.Gamma (1 + x) / Real.sqrt Real.pi) ^ (6 : ℕ) -
    (8 * x ^ (3 : ℕ) + 4 * x ^ (2 : ℕ) + x)

end RamanujanLostNotebook.PartV


