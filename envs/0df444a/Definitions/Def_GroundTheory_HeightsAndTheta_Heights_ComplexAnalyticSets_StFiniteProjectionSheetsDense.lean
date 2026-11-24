-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionSheetsDense
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionSheetsDense
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:19.416364+00:00
-- url     : https://prove2.me/theorems/301f7a35-bdc1-4dde-a4ba-374044b29dc9
-- title:
--   St Finite Projection Sheets Dense
-- statement:
--   Definitions and structural lemmas for St Finite Projection Sheets Dense, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFiniteProjectionSheetsDense.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermProjectionImageNear
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
def FiniteProjectionSheetsDense.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∃ N ∈ 𝓝 w, X ∩ N ⊆ closure {y | y ∈ X ∧ ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
      (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ y ∈ V ∧ AnalyticOnNhd ℂ g O ∧
        (∀ t ∈ O, A (g t) = t) ∧ X ∩ V = g '' O}
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


