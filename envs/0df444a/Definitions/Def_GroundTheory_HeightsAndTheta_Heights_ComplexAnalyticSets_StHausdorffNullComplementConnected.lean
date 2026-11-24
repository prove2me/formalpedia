-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHausdorffNullComplementConnected
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHausdorffNullComplementConnected
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:24.758805+00:00
-- url     : https://prove2.me/theorems/cb3fce00-7363-485f-a34b-f8653b9f8afe
-- title:
--   St Hausdorff Null Complement Connected
-- statement:
--   Definitions and structural lemmas for St Hausdorff Null Complement Connected, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StHausdorffNullComplementConnected.lean

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
open Topology Metric MeasureTheory
def HausdorffNullComplementConnected.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (D C : Set E),
    IsOpen D → IsPreconnected D → μH[(Module.finrank ℝ E : ℝ) - 1] C = 0 → IsPreconnected (D \ C)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


