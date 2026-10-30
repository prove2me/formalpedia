-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13Y
-- name    : RamanujanLostNotebook_PartI_ch13_ch13Y
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T10:37:52.769497+00:00
-- url     : https://prove2.me/theorems/b17ecb39-b01b-4e82-a323-7f9106311d4a
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 13: ch13Y
-- statement:
--   y_i(q) selected by the source recursion, for i>=1. y_0 is unused and is zero.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 13.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13YVec

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- y_i(q) selected by the source recursion, for i>=1. y_0 is unused and is zero. -/
def ch13Y (q : ℂ) (i : ℕ) : ℂ := ch13YVec q i i

end RamanujanLostNotebook.PartI

end


