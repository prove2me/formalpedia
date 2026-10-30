-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10ZeroSum
-- name    : RamanujanLostNotebook_PartIII_ch10_ch10ZeroSum
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T12:30:36.205631+00:00
-- url     : https://prove2.me/theorems/f9a9dd42-9cff-4675-af22-9030115409d5
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 10: ch10ZeroSum
-- statement:
--   Unordered zero sum. Theorems explicitly assert summability whenever this is the intended source meaning.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 10.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10ZeroOrder
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10Zeros

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- Unordered zero sum. Theorems explicitly assert summability whenever this is the intended source meaning. -/
noncomputable def ch10ZeroSum (f g : ℂ → ℂ) : ℂ :=
  ∑' z : ch10Zeros f, (ch10ZeroOrder f z : ℂ) * g z

end RamanujanLostNotebook.PartIII

end


