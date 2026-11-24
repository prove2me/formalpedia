-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionCover
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionCover
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:12.680008+00:00
-- url     : https://prove2.me/theorems/23a86b5c-fa3f-4f34-ac98-9424a6945eb0
-- title:
--   St Finite Germ Projection Cover
-- statement:
--   Definitions and structural lemmas for St Finite Germ Projection Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFiniteGermProjectionCover.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LocalParametrisation
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
def FiniteGermProjectionCover.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∃ N₀ ∈ 𝓝 w, ∀ (B : Set (σ → ℂ)) (D : Set (Fin d → ℂ)),
      IsOpen B → B ⊆ N₀ → w ∈ X ∩ B → IsOpen D → IsPreconnected D → Set.MapsTo A (X ∩ B) D →
      (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) →
      (∀ x ∈ X ∩ B, A x = A w → x = w) →
      ∃ (δ : (Fin d → ℂ) → ℂ) (N : ℕ), IsLocalParametrisation X w B A D δ N
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


