-- Prove2me | Definitions.Def_JRCurvedQFT_Symmetries_IsFlowAction
-- name    : JRCurvedQFT_Symmetries_IsFlowAction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:04:56.805208+00:00
-- url     : https://prove2.me/theorems/cf9c8842-cc3d-4574-9fa6-c42a84cacb08
-- title:
--   Strongly continuous unitary action $\Gamma(\phi_\alpha)$ of a flow on $\mathcal E$
-- statement:
--   A family $\Gamma(\alpha)$ of unitaries of $\mathcal E$ is the **action of the flow** $\phi$ if
--   $$\Gamma(\alpha)\,\Phi(f_1)\cdots\Phi(f_n)=\Phi(f_1\circ\phi_{-\alpha})\cdots\Phi(f_n\circ\phi_{-\alpha})$$
--   and $\alpha\mapsto\Gamma(\alpha)F$ is continuous for every $F\in\mathcal E$. This is (2.2) with $f^\psi=f\circ\psi^{-1}$, and Assumption 2 restricted to the flow.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, Definition 2.2, p. 3; Assumption 2, p. 6

import Mathlib
import Definitions.Def_JRCurvedQFT_Symmetries_IsometryFlow
import Definitions.Def_JRCurvedQFT_Symmetries_fieldSpace

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory

namespace JRCurvedQFT.Symmetries

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `Γ` is the strongly continuous unitary action of the flow `φ` on `E`:
`Γ(φ_α) Φ(f₁)…Φ(f_n) = Φ(f₁∘φ_{−α})…Φ(f_n∘φ_{−α})` (from (2.2), `f^ψ = f ∘ ψ⁻¹`).

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, Definition 2.2, p. 3, and Assumption 2, p. 6: "The isometry groups G that we consider leave
the measure dµ invariant, in the sense that Γ, defined above, is a unitary representation of G on
E."

**Formalization Note** Reading 5: Assumption 2 is used only for `θ` and the flow, and "unitary
representation" is read in its standard sense, with `α ↦ Γ(φ_α)F` continuous; the proof of
Theorem 6.4 needs that continuity. Monomials span a dense subspace of `E`, so this rule determines
`Γ α`; the group law is a consequence. -/
structure IsFlowAction (φ : IsometryFlow (d := d) M) (Φ : EuclideanField (d := d) M P)
    (Γ : ℝ → (fieldSpace Φ ≃ₗᵢ[ℂ] fieldSpace Φ)) : Prop where
  monomial_rule : ∀ (α : ℝ) (n : ℕ) (f g : Fin n → testFunctions (d := d) M),
    (∀ i p, (g i : M → ℝ) p = (f i : M → ℝ) (φ.toFun (-α) p)) →
    Γ α (fieldMonomial Φ f) = fieldMonomial Φ g
  continuous_orbit : ∀ F, Continuous (fun α => Γ α F)

end JRCurvedQFT.Symmetries


