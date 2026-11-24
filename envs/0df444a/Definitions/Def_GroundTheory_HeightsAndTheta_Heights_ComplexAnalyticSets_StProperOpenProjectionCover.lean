-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperOpenProjectionCover
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperOpenProjectionCover
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:54:52.253397+00:00
-- url     : https://prove2.me/theorems/021d0756-66c8-4886-a937-87333b31d85a
-- title:
--   St Proper Open Projection Cover
-- statement:
--   Definitions and structural lemmas for St Proper Open Projection Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StProperOpenProjectionCover.lean

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
def ProperOpenProjectionCover.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    IsOpen D → IsPreconnected D → D.Nonempty → Set.MapsTo A (X ∩ B) D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∃ (δ : (Fin d → ℂ) → ℂ) (N : ℕ),
      AnalyticOnNhd ℂ δ D ∧ (∃ y ∈ D, δ y ≠ 0) ∧
      (∀ y ∈ D, δ y ≠ 0 → {x | x ∈ X ∩ B ∧ A x = y}.encard = N) ∧
      (∀ x ∈ X ∩ B, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
        IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ X ∩ B ∩ V = g '' O) ∧
      X ∩ B ⊆ closure {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0}
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


