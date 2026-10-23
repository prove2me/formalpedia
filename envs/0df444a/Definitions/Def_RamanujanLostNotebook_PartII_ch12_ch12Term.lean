-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Term
-- name    : RamanujanLostNotebook_PartII_ch12_ch12Term
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:23:54.030744+00:00
-- url     : https://prove2.me/theorems/01a20c45-d2a4-439f-b8cd-6a68f5f95d8c
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 12: ch12Term
-- statement:
--   One whole μ-term of (12.1.1), all representations grouped together as the
--   chapter specifies. Inadmissible μ, including zero, contribute zero.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 12.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Admissible
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12C
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12W

namespace RamanujanLostNotebook.PartII

/-- One whole μ-term of (12.1.1), all representations grouped together as the
chapter specifies. Inadmissible μ, including zero, contribute zero. -/
noncomputable def ch12Term (n mu : ℕ) : ℝ := by
  classical
  exact if ch12Admissible mu then
    2 / ch12C * ch12W n mu / (mu : ℝ) ^ 4 *
      Real.exp (2 * (n : ℝ) * Real.pi / mu) else 0

end RamanujanLostNotebook.PartII


