-- Prove2me | Definitions.Def_BrownianEnergyRep_IsInversionOperator
-- name    : BrownianEnergyRep_IsInversionOperator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:36.704641+00:00
-- url     : https://prove2.me/theorems/b9c40864-ca7e-4434-88d7-c7eea310a6db
-- title:
--   The inversion operator $J$ of (2.12)
-- statement:
--   $J$ is the operator $(Jf)(\gamma)=f\circ\Theta(\gamma)=f(\gamma^{-1})$ on $L^2(W(G),\mu)$. It is the unitary involution that intertwines $U^R$ and $U^L$.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, (2.12), p.9

import Mathlib
import Definitions.Def_BrownianEnergyRep_WienerGroup

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- `J` is the operator `(Jf)(γ) = f(γ⁻¹)` of (2.12) (arXiv:1511.07378v1, (2.12), p.9). -/
def IsInversionOperator {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {T : ℝ} [Fact (0 < T)]
    (μ : Measure ↥(WienerGroup G T)) (J : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ) : Prop :=
  ∀ f : Lp ℂ 2 μ, (J f : ↥(WienerGroup G T) → ℂ) =ᵐ[μ] fun γ => f γ⁻¹

end BrownianEnergyRep


