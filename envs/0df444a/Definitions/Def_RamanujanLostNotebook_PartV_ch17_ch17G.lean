-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17G
-- name    : RamanujanLostNotebook_PartV_ch17_ch17G
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:26:10.649508+00:00
-- url     : https://prove2.me/theorems/b5866926-08ec-46c9-bd67-db95c76a7dac
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 17: ch17G
-- statement:
--   Nonholomorphic correction from the vertical ray starting at minus conjugate tau.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 17.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17GTerm

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- Nonholomorphic correction from the vertical ray starting at minus conjugate tau. -/
noncomputable def ch17G (τ : ℂ) : Fin 3 → ℂ :=
  fun c => 2 * Complex.I * (Real.sqrt 3 : ℂ) * ∫ t in Set.Ioi (0 : ℝ), ch17GTerm τ c t

end RamanujanLostNotebook.PartV

end


