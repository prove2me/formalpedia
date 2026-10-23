-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10ZeroOrder
-- name    : RamanujanLostNotebook_PartIII_ch10_ch10ZeroOrder
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T12:25:56.102975+00:00
-- url     : https://prove2.me/theorems/79d459fe-43f7-40cd-949e-f80723b692e9
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 10: ch10ZeroOrder
-- statement:
--   Analytic zero multiplicity: the first nonvanishing complex derivative. Used only for analytic, nonidentically-zero zeta or L functions in the open critical strip.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 10.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- Analytic zero multiplicity: the first nonvanishing complex derivative. Used only for analytic, nonidentically-zero zeta or L functions in the open critical strip. -/
noncomputable def ch10ZeroOrder (f : ℂ → ℂ) (z : ℂ) : ℕ :=
  sInf {k : ℕ | iteratedDeriv k f z ≠ 0}

end RamanujanLostNotebook.PartIII

end


