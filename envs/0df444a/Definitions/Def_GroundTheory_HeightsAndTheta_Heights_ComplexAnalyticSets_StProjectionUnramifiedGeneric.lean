-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjectionUnramifiedGeneric
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjectionUnramifiedGeneric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:55.079439+00:00
-- url     : https://prove2.me/theorems/164ac950-0a7e-456d-848c-6bc1a6900393
-- title:
--   St Projection Unramified Generic
-- statement:
--   Definitions and structural lemmas for St Projection Unramified Generic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StProjectionUnramifiedGeneric.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StJacobianRankOffHypersurface
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
def ProjectionUnramifiedGeneric.Statement : Prop :=
  ∀ (α β : Type) [Fintype α] [Fintype β] (Q : Ideal (MvPolynomial (α ⊕ β) ℂ)) (r : ℕ)
    (q : Fin r → MvPolynomial (α ⊕ β) ℂ) (t : MvPolynomial (α ⊕ β) ℂ), Q.IsPrime →
    (∀ b : β, ∃ F : Polynomial (MvPolynomial α ℂ), F.Monic ∧
      F.eval₂ (rename Sum.inl : MvPolynomial α ℂ →ₐ[ℂ] MvPolynomial (α ⊕ β) ℂ).toRingHom (X (Sum.inr b)) ∈ Q) →
    (∀ j, q j ∈ Q) → t ∉ Q → (∀ p ∈ Q, ∃ i : ℕ, t ^ i * p ∈ Ideal.span (Set.range q)) →
      ∃ μ : MvPolynomial (α ⊕ β) ℂ, μ ∉ Q ∧ ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn Q, eval w μ ≠ 0 →
        ∀ v : α ⊕ β → ℂ, (∀ a : α, v (Sum.inl a) = 0) →
          (∀ j, ∑ s, eval w (pderiv s (q j)) * v s = 0) → v = 0
end
end GroundTheory.Heights₂.Heights


