-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:27.152663+00:00
-- url     : https://prove2.me/theorems/1f7b45cb-0cc9-4e23-be44-820967b88704
-- title:
--   St Analytic Germ Components
-- statement:
--   Definitions and structural lemmas for St Analytic Germ Components, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StAnalyticGermComponents.lean

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
def AnalyticGermComponents.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w → w ∈ X →
    ∃ (n : ℕ) (Y : Fin n → Set (σ → ℂ)), (∀ i, IsAnalyticNear (Y i) w ∧ GermIrreducibleAt (Y i) w) ∧
      ∃ W ∈ 𝓝 w, X ∩ W = (⋃ i, Y i) ∩ W
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


