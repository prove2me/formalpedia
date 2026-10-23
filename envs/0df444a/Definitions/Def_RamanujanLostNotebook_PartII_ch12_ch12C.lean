-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12C
-- name    : RamanujanLostNotebook_PartII_ch12_ch12C
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:18:56.692411+00:00
-- url     : https://prove2.me/theorems/5c788a0b-fc02-4297-846f-5e6a685dee24
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 12: ch12C
-- statement:
--   The constant C in (11.5.3), printed p.280: the weight-eight Eisenstein
--   series at exp(−2π). The summation starts at k=1, and the positive exponential
--   ensures each denominator is nonzero.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 12.

import Mathlib

namespace RamanujanLostNotebook.PartII

/-- The constant C in (11.5.3), printed p.280: the weight-eight Eisenstein
series at exp(−2π). The summation starts at k=1, and the positive exponential
ensures each denominator is nonzero. -/
noncomputable def ch12C : ℝ :=
  1 + 480 * ∑' k : ℕ,
    ((k + 1 : ℕ) : ℝ) ^ 7 / (Real.exp (2 * Real.pi * (k + 1)) - 1)

end RamanujanLostNotebook.PartII


