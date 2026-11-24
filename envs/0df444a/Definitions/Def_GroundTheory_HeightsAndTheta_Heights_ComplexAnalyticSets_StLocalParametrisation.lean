-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalParametrisation
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalParametrisation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:27.400499+00:00
-- url     : https://prove2.me/theorems/27eb297b-6371-4e0d-8ac6-55a76182eecf
-- title:
--   St Local Parametrisation
-- statement:
--   Definitions and structural lemmas for St Local Parametrisation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLocalParametrisation.lean

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
def LocalParametrisation.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w → GermIrreducibleAt X w →
    ∀ U ∈ 𝓝 w, ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (B : Set (σ → ℂ)) (D : Set (Fin d → ℂ))
      (δ : (Fin d → ℂ) → ℂ) (N : ℕ), B ⊆ U ∧ IsLocalParametrisation X w B A D δ N
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


