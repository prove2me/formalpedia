-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFibreDiscriminantHolomorphic
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFibreDiscriminantHolomorphic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:16.856803+00:00
-- url     : https://prove2.me/theorems/a4a000c1-aa35-4179-a9de-2e6e32c160c5
-- title:
--   St Fibre Discriminant Holomorphic
-- statement:
--   Definitions and structural lemmas for St Fibre Discriminant Holomorphic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFibreDiscriminantHolomorphic.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GenericCountCover
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
def FibreDiscriminantHolomorphic.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ))
    (N : ℕ) (l : (σ → ℂ) →L[ℂ] ℂ),
    IsOpen D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    (∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x)) →
    IsGenericCountCover Y A D N →
    AnalyticOnNhd ℂ (fibreDiscr Y A l N) D
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


