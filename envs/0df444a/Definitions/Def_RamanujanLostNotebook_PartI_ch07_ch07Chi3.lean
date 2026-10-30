-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Chi3
-- name    : RamanujanLostNotebook_PartI_ch07_ch07Chi3
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T04:53:53.183127+00:00
-- url     : https://prove2.me/theorems/f83147b4-d538-456d-b80b-f7e391acf1fb
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 7: ch07Chi3
-- statement:
--   The quadratic odd character modulo 3: residues 0,1,2 have values 0,1,-1, respectively. Used in Entry 7.3.1; χ(0)=0.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 7.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The quadratic odd character modulo 3: residues 0,1,2 have values 0,1,-1, respectively. Used in Entry 7.3.1; χ(0)=0. -/
def ch07Chi3 (n : ℕ) : ℝ :=
  if n % 3 = 0 then 0 else if n % 3 = 1 then 1 else -1

end RamanujanLostNotebook.PartI

end


