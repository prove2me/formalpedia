-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch02_ch02SReal
-- name    : RamanujanLostNotebook_PartI_ch02_ch02SReal
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T09:33:07.596374+00:00
-- url     : https://prove2.me/theorems/8edf2471-1fee-4ad0-a9bb-f961250fa95f
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 2: ch02SReal
-- statement:
--   Positive-real S(q), with the signed real fifth root convention in S(q)=-R(-q). Values outside 0<q<1 are not used as source semantics.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 2.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch02_ch02S

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Positive-real S(q), with the signed real fifth root convention in S(q)=-R(-q). Values outside 0<q<1 are not used as source semantics. -/
noncomputable def ch02SReal (q : ℝ) : ℝ := (ch02S (q : ℂ) ((Real.rpow q (1 / 5 : ℝ) : ℝ) : ℂ)).re

end RamanujanLostNotebook.PartI

end


