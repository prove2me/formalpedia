-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch14_ch14Chi3
-- name    : RamanujanLostNotebook_PartI_ch14_ch14Chi3
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T02:40:58.680466+00:00
-- url     : https://prove2.me/theorems/03c2b1f0-5fef-4ccb-93b3-e7cd7631253c
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 14: ch14Chi3
-- statement:
--   The real quadratic character modulo 3: 0, 1, −1 on residues 0, 1, 2. This is the Legendre symbol in (14.3.1), printed p.318.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 14.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The real quadratic character modulo 3: 0, 1, −1 on residues 0, 1, 2. This is the Legendre symbol in (14.3.1), printed p.318. -/
def ch14Chi3 (n : ℕ) : ℤ :=
  if n % 3 = 0 then 0 else if n % 3 = 1 then 1 else -1

end RamanujanLostNotebook.PartI

end


