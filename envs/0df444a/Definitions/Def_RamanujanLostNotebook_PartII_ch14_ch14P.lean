-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch14_ch14P
-- name    : RamanujanLostNotebook_PartII_ch14_ch14P
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T04:36:17.245663+00:00
-- url     : https://prove2.me/theorems/b3d6e4ef-de4d-4e71-b299-e9a873d11365
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 14: ch14P
-- statement:
--   P=E₂ in the book's normalization (14.1.2), p.355: constant 1 and
--   Lambert multiplier -24. It is an analytic function on the open unit disk.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 14.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch14_ch14LambertTerm

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- P=E₂ in the book's normalization (14.1.2), p.355: constant 1 and
Lambert multiplier -24. It is an analytic function on the open unit disk. -/
noncomputable def ch14P (q : ℂ) : ℂ :=
  1 - 24 * ∑' n : ℕ, ch14LambertTerm 1 q n

end RamanujanLostNotebook.PartII

end


