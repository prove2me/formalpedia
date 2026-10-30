-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Count
-- name    : RamanujanLostNotebook_PartII_ch12_ch12Count
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-08T21:21:46.192466+00:00
-- url     : https://prove2.me/theorems/848f3258-948c-461b-949f-ab5b01405093
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 12: ch12Count
-- statement:
--   Rank of an admissible μ, or more generally the number of admissible positive
--   integers at most m. This counts integers, not representations (p.314).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 12.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Admissible

namespace RamanujanLostNotebook.PartII

/-- Rank of an admissible μ, or more generally the number of admissible positive
integers at most m. This counts integers, not representations (p.314). -/
noncomputable def ch12Count (m : ℕ) : ℕ := by
  classical
  exact ((Finset.range (m + 1)).filter ch12Admissible).card

end RamanujanLostNotebook.PartII


