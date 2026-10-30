-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch10_ch10ZTerm
-- name    : RamanujanLostNotebook_PartII_ch10_ch10ZTerm
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T08:39:57.564858+00:00
-- url     : https://prove2.me/theorems/c43fb751-3cbc-4677-bd0b-6b1be0fad8fe
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 10: ch10ZTerm
-- statement:
--   nth term of 2F1(1/2,1/2;1;k²). The binomial expression is exactly ((1/2)_n/n!)² k^(2n).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 10.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- nth term of 2F1(1/2,1/2;1;k²). The binomial expression is exactly ((1/2)_n/n!)² k^(2n). -/
noncomputable def ch10ZTerm (k : ℝ) (n : ℕ) : ℝ :=
  ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) ^ 2 * k ^ (2 * n)

end RamanujanLostNotebook.PartII

end


