-- Prove2me | Definitions.Def_SpectrumLB_prpState
-- name    : SpectrumLB_prpState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:15.977828+00:00
-- url     : https://prove2.me/theorems/6d6e9739-929e-4788-b5bf-776eca5a291e
-- title:
--   Random state $\rho=\widetilde X/\mathrm{Tr}(\widetilde X)$ (Definition 5.4)
-- statement:
--   The density matrix obtained by normalizing the product of random projections,
--
--   $$
--   \rho=\frac{X}{\mathrm{Tr}\,X},
--   $$
--
--   as a function of the unitaries $U_1,\dots,U_K$. Under the tilted law of Definition 5.4 this is the random state $\rho_a$ (or $\rho_b$) of the hard ensembles.
--
--   **Formalization Note** On the null event $X=0$ Lean's convention $0^{-1}=0$ gives the zero matrix.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Definition 5.4, p. 21

import Mathlib
import Definitions.Def_SpectrumLB_prpMatrix

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **The normalized state `ρ = X~ / Tr(X~)`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Definition 5.4, p. 21: "The random variable for a state sampled from the tilted law is denoted by
ρ := X~/Tr(X~)".

`prpState a U = (Tr X)⁻¹ X` with `X = prpMatrix a U`; the random state `ρ_a` is this map under
`tiltedHaar d n a`.

**Formalization Note.** At `Tr X = 0` (i.e. `X = 0`, a Haar-null event of tilted probability `0`) Lean's
`0⁻¹ = 0` gives the zero matrix. -/
noncomputable def prpState {d K : ℕ} (a : Fin K → ℕ) (U : Fin K → Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (prpMatrix a U).trace⁻¹ • prpMatrix a U

end SpectrumLB


