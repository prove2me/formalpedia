-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17F
-- name    : RamanujanLostNotebook_PartV_ch17_ch17F
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-08T21:18:42.028427+00:00
-- url     : https://prove2.me/theorems/303efd25-e312-45f2-a292-aeae86af4733
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 17: ch17F
-- statement:
--   Normalized three-component mock theta vector. Exponential parameters fix all fractional powers; the first component uses the squared denominator of the third-order function.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 17.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mockF3
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mockOmega3

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- Normalized three-component mock theta vector. Exponential parameters fix all fractional powers; the first component uses the squared denominator of the third-order function. -/
noncomputable def ch17F (τ : ℂ) : Fin 3 → ℂ :=
  ![Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * τ / 24) * mockF3 (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ)),
    2 * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ / 3) * mockOmega3 (Complex.exp ((Real.pi : ℂ) * Complex.I * τ)),
    2 * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ / 3) * mockOmega3 (-Complex.exp ((Real.pi : ℂ) * Complex.I * τ))]

end RamanujanLostNotebook.PartV

end


