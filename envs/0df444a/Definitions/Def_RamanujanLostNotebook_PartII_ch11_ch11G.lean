-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch11_ch11G
-- name    : RamanujanLostNotebook_PartII_ch11_ch11G
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T11:23:46.328989+00:00
-- url     : https://prove2.me/theorems/919a09c9-aff6-445d-ad31-6fcf82f66185
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 11: ch11G
-- statement:
--   G=R(-exp(-pi sqrt(3))), (11.3.5), written as a real Lambert series.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 11.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- G=R(-exp(-pi sqrt(3))), (11.3.5), written as a real Lambert series. -/
noncomputable def ch11G : ℝ :=
  1 - 504 * ∑' k : ℕ,
    (-1 : ℝ) ^ (k + 1) * ((k + 1 : ℕ) : ℝ) ^ 5 /
      (Real.exp ((k + 1) * Real.pi * Real.sqrt 3) - (-1 : ℝ) ^ (k + 1))

end RamanujanLostNotebook.PartII

end


