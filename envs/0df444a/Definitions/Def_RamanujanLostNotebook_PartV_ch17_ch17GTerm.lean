-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17GTerm
-- name    : RamanujanLostNotebook_PartV_ch17_ch17GTerm
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-08T21:22:59.515971+00:00
-- url     : https://prove2.me/theorems/b042a9b5-215d-4318-9643-70421c3ef436
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 17: ch17GTerm
-- statement:
--   Vertical-ray integrand for the nonholomorphic correction, including dz=i dt. The ray starts at minus the complex conjugate of tau.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 17.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17S
import Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17Theta

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- Vertical-ray integrand for the nonholomorphic correction, including dz=i dt. The ray starts at minus the complex conjugate of tau. -/
noncomputable def ch17GTerm (τ : ℂ) (c : Fin 3) (t : ℝ) : ℂ :=
  ch17S (ch17Theta (-star τ + Complex.I * t)) c /
    Complex.sqrt (-Complex.I * (-star τ + Complex.I * t + τ)) * Complex.I

end RamanujanLostNotebook.PartV

end


