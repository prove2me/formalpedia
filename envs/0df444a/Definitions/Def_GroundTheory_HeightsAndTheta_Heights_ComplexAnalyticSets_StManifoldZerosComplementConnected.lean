-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StManifoldZerosComplementConnected
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StManifoldZerosComplementConnected
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:46.539078+00:00
-- url     : https://prove2.me/theorems/6c586d4a-aa80-4865-934d-9c679472e5e0
-- title:
--   St Manifold Zeros Complement Connected
-- statement:
--   Definitions and structural lemmas for St Manifold Zeros Complement Connected, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StManifoldZerosComplementConnected.lean

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
def ManifoldZerosComplementConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (R : Set (σ → ℂ)) (h : (σ → ℂ) → ℂ),
    IsPreconnected R → (∀ x ∈ R, IsRegularPointOf R x) → (∀ x ∈ R, AnalyticAt ℂ h x) →
    (∃ x ∈ R, h x ≠ 0) → IsPreconnected (R \ {z | h z = 0})
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


