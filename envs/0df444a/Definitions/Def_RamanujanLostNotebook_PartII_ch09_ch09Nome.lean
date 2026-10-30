-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch09_ch09Nome
-- name    : RamanujanLostNotebook_PartII_ch09_ch09Nome
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T11:05:57.934342+00:00
-- url     : https://prove2.me/theorems/a1ab9a5d-5292-48ee-94fb-b84cf878f970
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 9: ch09Nome
-- statement:
--   Positive real nome q=exp(−π√(n/3)), (9.1.4), printed p.196.
--   Only n>0 is used, so 0<q<1.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 9.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Positive real nome q=exp(−π√(n/3)), (9.1.4), printed p.196.
Only n>0 is used, so 0<q<1. -/
noncomputable def ch09Nome (n : ℝ) : ℝ :=
  Real.exp (-Real.pi * Real.sqrt (n / 3))

end RamanujanLostNotebook.PartII

end


