-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreNear
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreNear
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:20.637277+00:00
-- url     : https://prove2.me/theorems/f5f99a85-8dcb-48e2-b78b-3210209a44cb
-- title:
--   St Isolated Fibre Near
-- statement:
--   Definitions and structural lemmas for St Isolated Fibre Near, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StIsolatedFibreNear.lean

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
def IsolatedFibreNear.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    ∃ N₀ ∈ 𝓝 w, ∀ x ∈ X ∩ N₀, ∃ W ∈ 𝓝 x, ∀ x' ∈ X ∩ W, A x' = A x → x' = x
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


