-- Prove2me | Definitions.Def_BrownianEnergyRep_IsGaussianRegularRep
-- name    : BrownianEnergyRep_IsGaussianRegularRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:15.029601+00:00
-- url     : https://prove2.me/theorems/06a4b1eb-74b5-4ebf-b487-116fc0117aec
-- title:
--   The Gaussian regular representation $U_{R,h}$ (corrected (5.1))
-- statement:
--   For $R\in O(W^*)$ and $h\in H$, the Gaussian regular representation of the Euclidean group on $L^2(W,\Gamma)$ is
--   $$
--   (U_{R,h}f)(w)=e^{\frac12\langle h,w\rangle-\frac14|h|^2}f\big((R^*)^{-1}(w-h)\big).
--   $$
--
--   **Formalization Note** The third line of (5.1) prints the factor $e^{\langle h,w\rangle-|h|^2/2}$, without the square root that its first two lines take. That factor is not unitary, and the proof of Proposition 5.5 uses the square root.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, (5.1), p.17 (corrected)

import Mathlib
import Definitions.Def_BrownianEnergyRep_AbstractWienerSpace
import Definitions.Def_BrownianEnergyRep_AbstractWienerSpace_pairing
import Definitions.Def_BrownianEnergyRep_Rotation

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- `U` is the Gaussian regular representation `U_{R,h}` of (5.1), corrected:
`(U_{R,h}f)(w) = e^{⟨h,w⟩/2 − |h|²/4} f((R*)⁻¹(w − h))` (arXiv:1511.07378v1, (5.1), p.17, corrected).

**Formalization Note** The third line of (5.1) prints `e^{⟨h,w⟩ − |h|²/2}`, which drops the square root
of the first two lines; the proof of Proposition 5.5 uses the square root. -/
def IsGaussianRegularRep {H W : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] (A : AbstractWienerSpace H W) (ρ : Rotation A) (h : H)
    (U : Lp ℂ 2 A.Γ ≃ₗᵢ[ℂ] Lp ℂ 2 A.Γ) : Prop :=
  ∀ f : Lp ℂ 2 A.Γ, (U f : W → ℂ) =ᵐ[A.Γ]
    fun w => (Real.exp (A.pairing h w / 2 - ‖h‖ ^ 2 / 4) : ℝ) * f (ρ.adj.symm (w - A.j h))

end BrownianEnergyRep


