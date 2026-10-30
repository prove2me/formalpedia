-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch15_ch15V15
-- name    : RamanujanLostNotebook_PartI_ch15_ch15V15
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T09:13:54.779343+00:00
-- url     : https://prove2.me/theorems/87efbf52-8a0a-4c08-b585-9a158cf6d6bb
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 15: ch15V15
-- statement:
--   v(q) in (15.7.1), p.349; distinct from the v of (15.7.30). The defining products converge and their denominator factors are nonzero for 0<q<1; definitions outside that domain are not source values.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 15.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch15_ch15F

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- v(q) in (15.7.1), p.349; distinct from the v of (15.7.30). The defining products converge and their denominator factors are nonzero for 0<q<1; definitions outside that domain are not source values. -/
def ch15V15 (q : ℝ) : ℝ :=
  q * (ch15F q * ch15F (q ^ 15) / (ch15F (q ^ 3) * ch15F (q ^ 5))) ^ 3

end RamanujanLostNotebook.PartI

end


