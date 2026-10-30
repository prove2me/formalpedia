-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch15_ch15P
-- name    : RamanujanLostNotebook_PartII_ch15_ch15P
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T07:09:18.486843+00:00
-- url     : https://prove2.me/theorems/46e2d5c7-3de0-4b75-9b7a-55d78e05e559
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 15: ch15P
-- statement:
--   Ramanujan's P at a real argument, the real part of its complex Lambert definition. The source uses real nomes in this chapter; absolute convergence is recorded separately. Normalization: P=1-24∑_(r≥1) r^1q^r/(1-q^r).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 15.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch15_ch15LambertTerm

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Ramanujan's P at a real argument, the real part of its complex Lambert definition. The source uses real nomes in this chapter; absolute convergence is recorded separately. Normalization: P=1-24∑_(r≥1) r^1q^r/(1-q^r). -/
noncomputable def ch15P (q : ℝ) : ℝ :=
  (1 + (-24 : ℂ) * ∑' r : ℕ, ch15LambertTerm 1 (q : ℂ) r).re

end RamanujanLostNotebook.PartII

end


