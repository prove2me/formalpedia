-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch04_ch04DiffTerm
-- name    : RamanujanLostNotebook_PartIII_ch04_ch04DiffTerm
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T07:49:55.721984+00:00
-- url     : https://prove2.me/theorems/05fdc70a-4ec9-4c68-9613-02ac2b6eaf3e
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 4: ch04DiffTerm
-- statement:
--   One summand of (4.2.4), with m=t.1+1 and n=t.2. A single product-index
--   family records absolute convergence of the double sum rather than an iterated junk value.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 4.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch04_ch04Sym

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- One summand of (4.2.4), with m=t.1+1 and n=t.2. A single product-index
family records absolute convergence of the double sum rather than an iterated junk value. -/
def ch04DiffTerm (a q : ℂ) (t : ℕ × ℕ) : ℂ :=
  let m := t.1 + 1
  let n := t.2
  (-1 : ℂ) ^ m * q ^ (m * (m + 1) / 2 + m * n) *
    (ch04Sym a (n + 1) - ch04Sym a n)

end RamanujanLostNotebook.PartIII

end


