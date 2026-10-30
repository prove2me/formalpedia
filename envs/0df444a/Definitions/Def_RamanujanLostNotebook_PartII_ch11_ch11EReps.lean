-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch11_ch11EReps
-- name    : RamanujanLostNotebook_PartII_ch11_ch11EReps
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T11:23:33.042985+00:00
-- url     : https://prove2.me/theorems/158796a8-91b2-4e8c-8e60-93bf90f8d9c9
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 11: ch11EReps
-- statement:
--   One representative c>2d>0 of each primitive Eisenstein orbit. This wedge
--   avoids division by 2d-c=0. Norms 1 and 3 are treated separately.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 11.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- One representative c>2d>0 of each primitive Eisenstein orbit. This wedge
avoids division by 2d-c=0. Norms 1 and 3 are treated separately. -/
def ch11EReps (la : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (la + 1)).product (Finset.range (la + 1))).filter
    (fun cd => 0 < cd.2 ∧ 2 * cd.2 < cd.1 ∧
      cd.1 ^ 2 + cd.2 ^ 2 = la + cd.1 * cd.2 ∧ Nat.Coprime cd.1 cd.2)

end RamanujanLostNotebook.PartII

end


