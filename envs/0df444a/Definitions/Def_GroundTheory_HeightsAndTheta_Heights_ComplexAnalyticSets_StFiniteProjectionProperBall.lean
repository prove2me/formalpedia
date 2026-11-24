-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionProperBall
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionProperBall
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:49:00.699675+00:00
-- url     : https://prove2.me/theorems/1fb6de9b-a852-4ed1-a19a-7a5f29667507
-- title:
--   St Finite Projection Proper Ball
-- statement:
--   Definitions and structural lemmas for St Finite Projection Proper Ball, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFiniteProjectionProperBall.lean

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
open Topology
def FiniteProjectionProperBall.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    ∀ U ∈ 𝓝 w, ∃ ρ : ℝ, 0 < ρ ∧ ∃ r : ℝ, 0 < r ∧ Metric.ball w ρ ⊆ U ∧
      ∀ K ⊆ Metric.ball (A w) r, IsCompact K →
        IsCompact {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ K}
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


