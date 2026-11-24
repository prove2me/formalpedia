-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCodimOneCompleteIntersection
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCodimOneCompleteIntersection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:57:22.039846+00:00
-- url     : https://prove2.me/theorems/1f9b26af-f436-477a-a461-d53c7c7d2cb7
-- title:
--   St Normal Codim One Complete Intersection
-- statement:
--   Definitions and structural lemmas for St Normal Codim One Complete Intersection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalCodimOneCompleteIntersection.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelDivisorGoodPoint
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
def NormalCodimOneCompleteIntersection.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P Q : Ideal (MvPolynomial σ ℂ)) (e : ℕ), P.IsPrime → Q.IsPrime → P ≤ Q →
    IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ P) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ P) = (e + 1 : ℕ) → ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = (e : ℕ) →
      ∃ (c : ℕ) (f : Fin c → MvPolynomial σ ℂ) (h : MvPolynomial σ ℂ),
        c + (e + 1) = Fintype.card σ ∧ (∀ j, f j ∈ P) ∧ h ∉ Q ∧
          ∀ p ∈ P, ∃ k : ℕ, h ^ k * p ∈ Ideal.span (Set.range f)
def lineOriginIdeal : Ideal (MvPolynomial (Fin 1 ⊕ Fin 1) ℂ) :=
  RingHom.ker (eval (0 : Fin 1 ⊕ Fin 1 → ℂ))
instance lineOriginIdeal_isMaximal : lineOriginIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨C c, eval_C c⟩
end
end GroundTheory.Heights₂.Heights


