-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperOpenProjectionLocalCover
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperOpenProjectionLocalCover
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:15:45.873548+00:00
-- url     : https://prove2.me/theorems/35a083fd-e854-4813-933d-52ea61d15c52
-- title:
--   St Proper Open Projection Local Cover
-- statement:
--   Definitions and structural lemmas for St Proper Open Projection Local Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StProperOpenProjectionLocalCover.lean

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
def ProperOpenProjectionLocalCover.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    IsOpen D → Set.MapsTo A (X ∩ B) D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∀ y₀ ∈ D, ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → ℂ) (n : ℕ),
      IsOpen U ∧ y₀ ∈ U ∧ U ⊆ D ∧ AnalyticOnNhd ℂ g U ∧
      (∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, g t ≠ 0) ∧
      (∀ y ∈ U, {x | x ∈ X ∩ B ∧ A x = y}.encard ≤ n) ∧
      ∀ y ∈ U, g y ≠ 0 → {x | x ∈ X ∩ B ∧ A x = y}.encard = n ∧
        ∀ x ∈ X ∩ B, A x = y → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
          IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧
          X ∩ B ∩ V = h '' O
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


