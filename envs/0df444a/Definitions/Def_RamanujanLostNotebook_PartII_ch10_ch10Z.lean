-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch10_ch10Z
-- name    : RamanujanLostNotebook_PartII_ch10_ch10Z
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T08:43:07.04104+00:00
-- url     : https://prove2.me/theorems/a90c8287-8cd1-47d6-8871-8d5e5c0dd989
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 10: ch10Z
-- statement:
--   The Gaussian series z in (10.5.1); convergence is asserted by statements, never assumed merely from this totalized sum.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 10.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch10_ch10ZTerm

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- The Gaussian series z in (10.5.1); convergence is asserted by statements, never assumed merely from this totalized sum. -/
noncomputable def ch10Z (k : ℝ) : ℝ := ∑' n : ℕ, ch10ZTerm k n

end RamanujanLostNotebook.PartII

end


