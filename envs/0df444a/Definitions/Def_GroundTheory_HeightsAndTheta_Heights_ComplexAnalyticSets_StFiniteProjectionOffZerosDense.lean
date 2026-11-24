-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionOffZerosDense
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionOffZerosDense
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:57.406259+00:00
-- url     : https://prove2.me/theorems/018d3da6-210d-4b80-a877-8c02b9664944
-- title:
--   St Finite Projection Off Zeros Dense
-- statement:
--   Definitions and structural lemmas for St Finite Projection Off Zeros Dense, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFiniteProjectionOffZerosDense.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionSheetsDense
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
def FiniteProjectionOffZerosDense.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∀ δ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ δ (A w) → (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) →
      ∃ N ∈ 𝓝 w, X ∩ N ⊆ closure {z | z ∈ X ∧ δ (A z) ≠ 0}
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


