-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch15_ch15Q
-- name    : RamanujanLostNotebook_PartII_ch15_ch15Q
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T07:09:39.998441+00:00
-- url     : https://prove2.me/theorems/ccf8e17b-9ea1-4c6e-83cf-5dab64deef3a
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 15: ch15Q
-- statement:
--   Ramanujan's Q at a real argument, the real part of its complex Lambert definition. The source uses real nomes in this chapter; absolute convergence is recorded separately. Normalization: Q=1+240∑_(r≥1) r^3q^r/(1-q^r).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 15.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch15_ch15LambertTerm

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Ramanujan's Q at a real argument, the real part of its complex Lambert definition. The source uses real nomes in this chapter; absolute convergence is recorded separately. Normalization: Q=1+240∑_(r≥1) r^3q^r/(1-q^r). -/
noncomputable def ch15Q (q : ℝ) : ℝ :=
  (1 + (240 : ℂ) * ∑' r : ℕ, ch15LambertTerm 3 (q : ℂ) r).re

end RamanujanLostNotebook.PartII

end


