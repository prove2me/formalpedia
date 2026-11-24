-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicOnSubset
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicOnSubset
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:53.170509+00:00
-- url     : https://prove2.me/theorems/7e5f599c-cd29-4eda-9183-3d3a9adbf563
-- title:
--   St Holomorphic On Subset
-- statement:
--   Definitions and structural lemmas for St Holomorphic On Subset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StHolomorphicOnSubset.lean

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
def HolomorphicOnSubset {σ : Type*} [Fintype σ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : (σ → ℂ) → E) (S : Set (σ → ℂ)) : Prop :=
  ∀ z ∈ S, ∃ U : Set (σ → ℂ), IsOpen U ∧ z ∈ U ∧ ∃ F : (σ → ℂ) → E,
    DifferentiableOn ℂ F U ∧ Set.EqOn f F (S ∩ U)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


