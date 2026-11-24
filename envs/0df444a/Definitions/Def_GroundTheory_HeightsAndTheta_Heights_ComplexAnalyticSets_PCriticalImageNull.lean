-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:31.983829+00:00
-- url     : https://prove2.me/theorems/dbcf285a-8848-49ab-bfd9-41ba1f50fab4
-- title:
--   PCritical Image Null
-- statement:
--   Definitions and structural lemmas for PCritical Image Null, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCriticalImageNull.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
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
open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
noncomputable section
section Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def shrinkAlong (i0 : ι) (k : ι → ℝ) (δ : ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.id - (1 - δ) • (LinearMap.proj i0 : (ι → ℝ) →ₗ[ℝ] ℝ).smulRight k
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
end Real
section Global
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
variable [SecondCountableTopology F]
end Global
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


