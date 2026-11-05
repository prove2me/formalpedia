-- Prove2me | Definitions.Def_BrownianEnergyRep_IsEnergyRep
-- name    : BrownianEnergyRep_IsEnergyRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:04:55.17357+00:00
-- url     : https://prove2.me/theorems/2746aa0f-bf29-4458-9032-979f0330de9d
-- title:
--   The energy representation $E$ (corrected Definition 5.7)
-- statement:
--   The energy representation acts on complex $L^2(W(\mathfrak g),\nu)$ by
--   $$
--   (E_\varphi f)(w)=\exp\Big(\frac i2\int_0^T\langle\varphi'\varphi^{-1}(s),dw_s\rangle\Big)\,f\big(O_{\varphi^{-1}}w\big).
--   $$
--   It is the object that the main theorem compares with the Brownian representations.
--
--   **Formalization Note** This is a correction of Definition 5.7, which prints the phase $\exp\big(i\int_0^T\langle\varphi^{-1}\varphi'(s),dw_s\rangle\big)$. The integrand must be $\varphi'\varphi^{-1}$, because the printed one fails the cocycle identity on $SO(3)$, so that $E$ is not a homomorphism. The coefficient must be $\tfrac12$, because on $SO(2)$ the printed one gives a representation not equivalent to $U^R$. The factor $\tfrac12$ is the one produced by Proposition 5.5.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Definition 5.7, p.18 (corrected)

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_WienerGroup
import Definitions.Def_BrownianEnergyRep_FiniteEnergy
import Definitions.Def_BrownianEnergyRep_WienerPath
import Definitions.Def_BrownianEnergyRep_rotation__ef917c
import Definitions.Def_BrownianEnergyRep_wienerIntegral

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- `En` is the energy representation, in the corrected normalization
`(E_ϕ f)(w) = exp((i/2) ∫₀ᵀ ⟨ϕ′ϕ⁻¹(s), dw_s⟩) f(O_{ϕ⁻¹} w)` on complex `L²(W(𝔤), ν)`
(arXiv:1511.07378v1, Definition 5.7, p.18, corrected).

**Formalization Note** The page prints the phase `exp(i ∫₀ᵀ ⟨ϕ⁻¹ϕ′(s), dw_s⟩)`. With that phase
`E` is not a homomorphism (`G = SO(3)`) and not equivalent to `U^R` (`G = SO(2)`), so the coefficient is
`1/2` and the integrand is `ϕ′ϕ⁻¹`. -/
def IsEnergyRep {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : MatrixLieAlgebra G E)
    {T : ℝ} [Fact (0 < T)] (ν : Measure ↥(WienerPath E T))
    (En : ↥(WienerGroup G T) → (Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 ν)) : Prop :=
  ∀ ϕ ∈ FiniteEnergy L T, ∀ f : Lp ℂ 2 ν,
    (En ϕ f : ↥(WienerPath E T) → ℂ) =ᵐ[ν]
      fun w => Complex.exp (Complex.I / 2 * (wienerIntegral ν (rightLog L ϕ) w : ℂ)) *
        f (rotation L ϕ⁻¹ w)

end BrownianEnergyRep


