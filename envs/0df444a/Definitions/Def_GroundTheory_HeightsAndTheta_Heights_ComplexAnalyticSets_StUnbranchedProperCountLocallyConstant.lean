-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountLocallyConstant
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountLocallyConstant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:15:45.823203+00:00
-- url     : https://prove2.me/theorems/a9014165-3689-4372-a61c-52e28b3c0b7d
-- title:
--   St Unbranched Proper Count Locally Constant
-- statement:
--   Definitions and structural lemmas for St Unbranched Proper Count Locally Constant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StUnbranchedProperCountLocallyConstant.lean

import Mathlib
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
open Topology
def UnbranchedProperCountLocallyConstant.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ),
    IsOpen D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    (∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ ContinuousOn g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O) →
    ∀ y ∈ D, δ y ≠ 0 → {x | x ∈ Y ∧ A x = y}.Finite ∧
      ∀ᶠ y' in 𝓝 y, {x | x ∈ Y ∧ A x = y'}.encard = {x | x ∈ Y ∧ A x = y}.encard
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


