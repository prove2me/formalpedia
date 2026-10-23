-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Phase
-- name    : RamanujanLostNotebook_PartII_ch12_ch12Phase
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:21:28.409364+00:00
-- url     : https://prove2.me/theorems/ab533d9c-09f1-436c-9894-12f6fa9be6a9
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 12: ch12Phase
-- statement:
--   The integer ac+bd, choosing a=ch12Inverse c d and b=(ad−1)/c, hence
--   ad−bc=1 on the primitive representative locus. Integer subtraction is essential.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 12.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Inverse

namespace RamanujanLostNotebook.PartII

/-- The integer ac+bd, choosing a=ch12Inverse c d and b=(ad−1)/c, hence
ad−bc=1 on the primitive representative locus. Integer subtraction is essential. -/
def ch12Phase (c d : ℕ) : ℤ :=
  let a : ℤ := ch12Inverse c d
  a * c + ((a * d - 1) / (c : ℤ)) * d

end RamanujanLostNotebook.PartII


