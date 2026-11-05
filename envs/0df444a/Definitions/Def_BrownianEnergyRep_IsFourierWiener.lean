-- Prove2me | Definitions.Def_BrownianEnergyRep_IsFourierWiener
-- name    : BrownianEnergyRep_IsFourierWiener
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:19.255461+00:00
-- url     : https://prove2.me/theorems/374710cb-d497-4c34-b7be-b3cdf7cf07f8
-- title:
--   The Fourier-Wiener transform $\mathcal F$
-- statement:
--   For $\varphi\in W^*$, put $\widehat\varphi(w)=e^{i\langle\varphi,w\rangle}$. The Fourier-Wiener transform is the unitary $\mathcal F$ of $L^2(W,\Gamma)$ with
--   $$
--   (\mathcal F\widehat\varphi)(w)=e^{-|\varphi|^2_{H^*}}e^{-\langle\varphi,w\rangle}.
--   $$
--   It conjugates the Gaussian regular representation to the energy representation.
--
--   **Formalization Note** The paper refers to Definition 17 of Driver-Hall for $\mathcal F$ and warns about its integral formula, so here $\mathcal F$ is defined by the second identity of (5.2). Proposition 5.4 of this mission says that such a unitary exists and is unique, since both families have Gram matrix $\exp(-\tfrac12|\varphi-\psi|^2)$ and both are total.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, p.17, (5.2)

import Mathlib
import Definitions.Def_BrownianEnergyRep_AbstractWienerSpace

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- The exponential `φ̂(w) = e^{i⟨φ,w⟩}` (arXiv:1511.07378v1, Proposition 5.4, p.17). -/
noncomputable def hat {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : StrongDual ℝ W) : W → ℂ :=
  fun w => Complex.exp (Complex.I * (φ w : ℂ))

/-- `F` is the Fourier-Wiener transform on `L²(W, Γ)` (arXiv:1511.07378v1, p.17 and (5.2)).

**Formalization Note** The paper refers to Definition 17 of Driver-Hall and warns about its integral
formula. Here `F` is the unitary with `Fφ̂ = e^{−|φ|²_{H*}} e^{−⟨φ,·⟩}`, the second identity of (5.2);
`proposition_5_4` says it exists and is unique. The hypothesis `hφ` holds for every `φ`, as `φ̂` is bounded. -/
def IsFourierWiener {H W : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] (A : AbstractWienerSpace H W) (F : Lp ℂ 2 A.Γ ≃ₗᵢ[ℂ] Lp ℂ 2 A.Γ) : Prop :=
  ∀ (φ : StrongDual ℝ W) (hφ : MemLp (hat φ) 2 A.Γ),
    (F (hφ.toLp _) : W → ℂ) =ᵐ[A.Γ]
      fun w => (Real.exp (-‖φ.comp A.j‖ ^ 2) * Real.exp (-φ w) : ℝ)

end BrownianEnergyRep


