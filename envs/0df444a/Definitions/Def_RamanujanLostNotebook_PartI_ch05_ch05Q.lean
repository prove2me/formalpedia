-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch05_ch05Q
-- name    : RamanujanLostNotebook_PartI_ch05_ch05Q
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T06:55:07.929864+00:00
-- url     : https://prove2.me/theorems/d49120f1-aa6d-418a-97b4-e3984baf6e6e
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 5: ch05Q
-- statement:
--   The canonical denominator Qₙ; a numerical approximant is meaningful only where this value is nonzero. Source: (5.1.2)–(5.1.3), p.125.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 5.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch05_ch05Continuants

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The canonical denominator Qₙ; a numerical approximant is meaningful only where this value is nonzero. Source: (5.1.2)–(5.1.3), p.125. -/
def ch05Q (b0 : ℂ) (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  (ch05Continuants b0 a b n).2.2

end RamanujanLostNotebook.PartI

end


