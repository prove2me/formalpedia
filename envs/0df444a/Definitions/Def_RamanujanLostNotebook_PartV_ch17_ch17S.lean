-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17S
-- name    : RamanujanLostNotebook_PartV_ch17_ch17S
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:18:26.927979+00:00
-- url     : https://prove2.me/theorems/c78a2782-7a81-4b52-9e63-e78db92fba51
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 17: ch17S
-- statement:
--   Inversion matrix: exchange the first two components and negate the third.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 17.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- Inversion matrix: exchange the first two components and negate the third. -/
noncomputable def ch17S (v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![v 1, v 0, -v 2]

end RamanujanLostNotebook.PartV

end


