-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13YVec
-- name    : RamanujanLostNotebook_PartI_ch13_ch13YVec
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T10:34:16.372176+00:00
-- url     : https://prove2.me/theorems/bbc3aefb-236e-445c-ba8f-9742cdc459aa
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 13: ch13YVec
-- statement:
--   Solve the triangular recursion successively: the coefficient of the newest y is
--   -theta_(1,1). Uncomputed indices and index zero are set to zero for bookkeeping.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 13.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13Rec
import Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13ThetaScaled

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Solve the triangular recursion successively: the coefficient of the newest y is
-theta_(1,1). Uncomputed indices and index zero are set to zero for bookkeeping. -/
def ch13YVec (q : ℂ) : ℕ → (ℕ → ℂ)
  | 0 => fun _ => 0
  | M + 1 => fun i => if i = M + 1 then
      ch13Rec q (ch13YVec q M) (M + 1) / ch13ThetaScaled 1 1 0 q
    else ch13YVec q M i

end RamanujanLostNotebook.PartI

end


