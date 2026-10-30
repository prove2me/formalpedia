-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17H
-- name    : RamanujanLostNotebook_PartV_ch17_ch17H
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-08T21:27:07.937462+00:00
-- url     : https://prove2.me/theorems/ac8e11c3-1e48-410f-9e3e-ba0da4d1b708
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 17: ch17H
-- statement:
--   Completed three-component function F-G on the upper half-plane.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 17.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17F
import Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17G

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- Completed three-component function F-G on the upper half-plane. -/
noncomputable def ch17H (τ : ℂ) : Fin 3 → ℂ :=
  ch17F τ - ch17G τ

end RamanujanLostNotebook.PartV

end


