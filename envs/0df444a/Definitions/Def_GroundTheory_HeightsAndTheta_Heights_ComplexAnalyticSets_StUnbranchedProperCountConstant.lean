-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:55.205042+00:00
-- url     : https://prove2.me/theorems/7c8e8dbe-babe-466b-96ac-cf03e79bf7ff
-- title:
--   St Unbranched Proper Count Constant
-- statement:
--   Definitions and structural lemmas for St Unbranched Proper Count Constant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StUnbranchedProperCountConstant.lean

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
def UnbranchedProperCountConstant.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ),
    IsOpen D → IsPreconnected D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    AnalyticOnNhd ℂ δ D →
    (∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ ContinuousOn g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O) →
    ∃ N : ℕ, ∀ y ∈ D, δ y ≠ 0 → {x | x ∈ Y ∧ A x = y}.encard = N
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


