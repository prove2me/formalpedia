-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicZeroSetDimH
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicZeroSetDimH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:47.443893+00:00
-- url     : https://prove2.me/theorems/f0166683-16b7-403b-b6cb-0406de4c7b21
-- title:
--   St Holomorphic Zero Set Dim H
-- statement:
--   Definitions and structural lemmas for St Holomorphic Zero Set Dim H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StHolomorphicZeroSetDimH.lean

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
open Topology Metric
open scoped ENNReal
def HolomorphicZeroSetDimH.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (h : (Fin k → ℂ) → ℂ),
    IsOpen U → DifferentiableOn ℂ h U →
    (∀ W ⊆ U, IsOpen W → W.Nonempty → ∃ w ∈ W, h w ≠ 0) →
      dimH {v | v ∈ U ∧ h v = 0} ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


