-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothPartialLifts
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothPartialLifts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:39.525482+00:00
-- url     : https://prove2.me/theorems/50c293e7-8d0c-4d05-9959-3703eddb8f72
-- title:
--   PPerfect Field Extension Formally Smooth Partial Lifts
-- statement:
--   Definitions and structural lemmas for PPerfect Field Extension Formally Smooth Partial Lifts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPerfectFieldExtensionFormallySmoothPartialLifts.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothFrobeniusLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Polynomial IntermediateField
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
variable {F K B : Type*} [Field F] [Field K] [Algebra F K] [CommRing B] [Algebra F B]
def IsGoodPartialLift (p : ℕ) (N : Ideal B) (u : K →ₐ[F] B ⧸ N) (ψ : K →+* B)
    (σ : Σ L : IntermediateField F K, L →ₐ[F] B) : Prop :=
  (∀ z : K, ∃ h : z ^ p ∈ σ.1, σ.2 ⟨z ^ p, h⟩ = ψ z) ∧ ∀ y : σ.1, Ideal.Quotient.mk N (σ.2 y) = u y
def PartialLiftLE (σ τ : Σ L : IntermediateField F K, L →ₐ[F] B) : Prop :=
  ∃ h : σ.1 ≤ τ.1, ∀ y : σ.1, τ.2 (IntermediateField.inclusion h y) = σ.2 y
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


