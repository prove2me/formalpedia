-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StComponentsGenericCount
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StComponentsGenericCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:52.71822+00:00
-- url     : https://prove2.me/theorems/c7a78bc3-6362-4f57-8f82-3e4819a1533e
-- title:
--   St Components Generic Count
-- statement:
--   Definitions and structural lemmas for St Components Generic Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StComponentsGenericCount.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets
def ComponentsGenericCount.Statement : Prop :=
  ∀ (n d : ℕ) (F : Finset (Ideal (MvPolynomial (Fin n) ℂ))) (A : Matrix (Fin d) (Fin n) ℂ),
    (∀ J ∈ F, J.IsPrime ∧ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d : ℕ) ∧ IsFiniteProjection J A) →
    (∀ J ∈ F, ∀ J' ∈ F, J ≤ J' → J = J') →
      (∀ y : Fin d → ℂ,
        {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y}.encard ≤ ((∑ J ∈ F, projDegree J A : ℕ) : ℕ∞)) ∧
      ∃ Δ : MvPolynomial (Fin d) ℂ, Δ ≠ 0 ∧ ∀ y : Fin d → ℂ, eval y Δ ≠ 0 →
        {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y}.encard = ((∑ J ∈ F, projDegree J A : ℕ) : ℕ∞) ∧
        ∀ x, (∃ J ∈ F, x ∈ zeroSet J) → A *ᵥ x = y →
          ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧
            DifferentiableOn ℂ g U ∧ g y = x ∧ ∀ y' ∈ U, A *ᵥ g y' = y' ∧ ∃ J ∈ F, g y' ∈ zeroSet J
end GroundTheory.Heights₂.Heights


