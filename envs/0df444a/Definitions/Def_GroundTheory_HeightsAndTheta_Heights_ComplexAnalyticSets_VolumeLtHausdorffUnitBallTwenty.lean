-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_VolumeLtHausdorffUnitBallTwenty
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_VolumeLtHausdorffUnitBallTwenty
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:47.386173+00:00
-- url     : https://prove2.me/theorems/e09aa322-6472-47bc-953d-a17522ef0dca
-- title:
--   Volume Lt Hausdorff Unit Ball Twenty
-- statement:
--   Definitions and structural lemmas for Volume Lt Hausdorff Unit Ball Twenty, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/VolumeLtHausdorffUnitBallTwenty.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RingKrullDimQuotBotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_FrameProjEq
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
open MeasureTheory Measure Metric Module
open scoped ENNReal
noncomputable section
namespace AreaLinear
def LebesgueForm : Prop :=
  ∀ (k m : ℕ) (L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)),
    Function.Injective L → ∀ A : Set (EuclideanSpace ℝ (Fin k)),
      μH[(k : ℝ)] (L '' A) = ENNReal.ofReal (areaFactor L) * volume A
end AreaLinear
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


