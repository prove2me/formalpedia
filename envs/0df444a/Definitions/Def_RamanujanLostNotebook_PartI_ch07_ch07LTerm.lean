-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07LTerm
-- name    : RamanujanLostNotebook_PartI_ch07_ch07LTerm
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T04:53:33.541962+00:00
-- url     : https://prove2.me/theorems/6f53f89e-a992-4346-853e-c5b620079e8a
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 7: ch07LTerm
-- statement:
--   One full period of the real Dirichlet series L(s,χ). The period index m starts at 0; the sole index 0 is assigned 0 explicitly. Periodic grouping preserves the ordered L(1,χ), although its individual terms are not absolutely summable. For s>1 grouping agrees with the absolutely convergent ordinary series.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 7.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- One full period of the real Dirichlet series L(s,χ). The period index m starts at 0; the sole index 0 is assigned 0 explicitly. Periodic grouping preserves the ordered L(1,χ), although its individual terms are not absolutely summable. For s>1 grouping agrees with the absolutely convergent ordinary series. -/
noncomputable def ch07LTerm (k : ℕ) (χ : ℕ → ℝ) (s m : ℕ) : ℝ :=
  ∑ r ∈ Finset.range k,
    if k * m + r = 0 then 0 else χ r / ((k * m + r : ℕ) : ℝ) ^ s

end RamanujanLostNotebook.PartI

end


