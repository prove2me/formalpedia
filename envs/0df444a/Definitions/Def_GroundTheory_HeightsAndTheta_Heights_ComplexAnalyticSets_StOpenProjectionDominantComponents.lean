-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOpenProjectionDominantComponents
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOpenProjectionDominantComponents
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:51.869269+00:00
-- url     : https://prove2.me/theorems/e84dda79-3b37-4f72-b452-94e6e1e44eef
-- title:
--   St Open Projection Dominant Components
-- statement:
--   Definitions and structural lemmas for St Open Projection Dominant Components, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StOpenProjectionDominantComponents.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
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
def OpenProjectionDominantComponents.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∀ w ∈ X ∩ B,
    ∃ (n : ℕ) (Y : Fin n → Set (σ → ℂ)),
      (∀ i, IsAnalyticNear (Y i) w ∧ GermIrreducibleAt (Y i) w ∧
        ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y i → h (A z) = 0) →
          ∀ᶠ y in 𝓝 (A w), h y = 0) ∧
      (∀ i j, i ≠ j → ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j) ∧
      ∃ W ∈ 𝓝 w, X ∩ B ∩ W = (⋃ i, Y i) ∩ W
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


