-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch15_ch15LambertConverges
-- name    : RamanujanLostNotebook_PartII_ch15_ch15LambertConverges
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T07:06:26.233257+00:00
-- url     : https://prove2.me/theorems/ab75299b-6bd8-4418-86cd-f299c77a62e2
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 15: ch15LambertConverges
-- statement:
--   Absolute convergence of the three defining Lambert families. This is concluded at the source nomes, never assumed to manufacture an identity.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 15.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch15_ch15LambertTerm

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Absolute convergence of the three defining Lambert families. This is concluded at the source nomes, never assumed to manufacture an identity. -/
def ch15LambertConverges (q : ℂ) : Prop :=
  Summable (ch15LambertTerm 1 q) ∧
  Summable (ch15LambertTerm 3 q) ∧ Summable (ch15LambertTerm 5 q)

end RamanujanLostNotebook.PartII

end


