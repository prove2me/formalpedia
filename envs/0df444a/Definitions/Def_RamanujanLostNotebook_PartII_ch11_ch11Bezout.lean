-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch11_ch11Bezout
-- name    : RamanujanLostNotebook_PartII_ch11_ch11Bezout
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T11:29:13.895121+00:00
-- url     : https://prove2.me/theorems/cc4ad15f-6590-4935-b74e-91fd5de67942
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 11: ch11Bezout
-- statement:
--   Canonical Bezout pair a,b with ad-bc=1. Integer subtraction and division
--   preserve the determinant; on the representative locus the quotient is exact.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 11.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch11_ch11Inverse

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Canonical Bezout pair a,b with ad-bc=1. Integer subtraction and division
preserve the determinant; on the representative locus the quotient is exact. -/
def ch11Bezout (c d : ℕ) : ℤ × ℤ :=
  let a : ℤ := ch11Inverse c d
  (a, (a * d - 1) / (c : ℤ))

end RamanujanLostNotebook.PartII

end


