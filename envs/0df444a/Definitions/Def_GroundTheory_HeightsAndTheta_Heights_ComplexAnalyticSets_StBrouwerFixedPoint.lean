-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBrouwerFixedPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBrouwerFixedPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:16.266823+00:00
-- url     : https://prove2.me/theorems/d1e1e848-c47d-4fe4-aa29-dd2a1c470c63
-- title:
--   St Brouwer Fixed Point
-- statement:
--   Definitions and structural lemmas for St Brouwer Fixed Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StBrouwerFixedPoint.lean

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
def BrouwerFixedPoint.Statement : Prop :=
  ∀ (n : ℕ) (f : (Fin n → ℝ) → Fin n → ℝ),
    ContinuousOn f (Metric.closedBall 0 1) →
      Set.MapsTo f (Metric.closedBall 0 1) (Metric.closedBall 0 1) →
        ∃ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1, f x = x
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


