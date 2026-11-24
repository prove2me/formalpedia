-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:24.614451+00:00
-- url     : https://prove2.me/theorems/15eac3d3-c940-4e49-babb-d889785c2775
-- title:
--   St Primitive Presentation Cover
-- statement:
--   Definitions and structural lemmas for St Primitive Presentation Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPrimitivePresentationCover.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermPrimitivePresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
def PrimitivePresentationCover.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (c : Fin N → (Fin d → ℂ) → ℂ)
    (δ : (Fin d → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (p i) w) → IsPrimitivePresentation w p A ℓ c δ →
    ∀ W ∈ 𝓝 w, ∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
      ∃ x : Fin N → σ → ℂ, (∀ j, x j ∈ W ∧ (∀ i, p i (x j) = 0) ∧ A (x j) = y) ∧
        Function.Injective fun j => ℓ (x j)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


