-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17ThetaTerm
-- name    : RamanujanLostNotebook_PartV_ch17_ch17ThetaTerm
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:18:31.649782+00:00
-- url     : https://prove2.me/theorems/9aba78a6-d4c2-4467-ba33-f00c81ba39cf
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 17: ch17ThetaTerm
-- statement:
--   The three weight-three-halves theta summands in the printed order g0,g1,g2. Integer powers encode the bilateral sign.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 17.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- The three weight-three-halves theta summands in the printed order g0,g1,g2. Integer powers encode the bilateral sign. -/
noncomputable def ch17ThetaTerm (z : ℂ) (c : Fin 3) (n : ℤ) : ℂ :=
  (![(-1 : ℂ)^n * ((n : ℂ) + 1/3) * Complex.exp (3 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1/3)^2 * z),
    -((n : ℂ) + 1/6) * Complex.exp (3 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1/6)^2 * z),
    ((n : ℂ) + 1/3) * Complex.exp (3 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1/3)^2 * z)] c)

end RamanujanLostNotebook.PartV

end


