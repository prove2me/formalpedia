-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch15_ch15Nome
-- name    : RamanujanLostNotebook_PartII_ch15_ch15Nome
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T07:05:59.601862+00:00
-- url     : https://prove2.me/theorems/d52b598f-4c43-4bba-b7cb-d688a183280c
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 15: ch15Nome
-- statement:
--   The positive nome exp(-π√n), used with a minus sign in Sections 15.2–15.4 and without a minus sign in Section 15.6. Only n>0 or eventual n→∞ is used.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 15.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- The positive nome exp(-π√n), used with a minus sign in Sections 15.2–15.4 and without a minus sign in Section 15.6. Only n>0 or eventual n→∞ is used. -/
noncomputable def ch15Nome (n : ℝ) : ℝ :=
  Real.exp (-Real.pi * Real.sqrt n)

end RamanujanLostNotebook.PartII

end


