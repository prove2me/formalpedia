-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusDense
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusDense
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:04.328381+00:00
-- url     : https://prove2.me/theorems/4680267b-6581-45d9-8a09-30ea61b56463
-- title:
--   St Regular Locus Dense
-- statement:
--   Definitions and structural lemmas for St Regular Locus Dense, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRegularLocusDense.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RegularLocus
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
def RegularLocusDense.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w →
    ∃ N : Set (σ → ℂ), IsOpen N ∧ w ∈ N ∧
      ∀ B : Set (σ → ℂ), IsOpen B → B ⊆ N → X ∩ B ⊆ closure (regLocus (X ∩ B))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


