-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTangentGraphLowerDensity
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTangentGraphLowerDensity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:09.830354+00:00
-- url     : https://prove2.me/theorems/3f5b5e53-a9f2-4531-9168-2fcf9cb5d82f
-- title:
--   PTangent Graph Lower Density
-- statement:
--   Definitions and structural lemmas for PTangent Graph Lower Density, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTangentGraphLowerDensity.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTangentGraphLowerDensity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyLelongMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
def TangentGraphLowerDensity.inPart {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ I :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : I => innerSL ℂ (b i))
def TangentGraphLowerDensity.outPart {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ {j : Fin n // j ∉ I} :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : {j : Fin n // j ∉ I} => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : {j : Fin n // j ∉ I} => innerSL ℂ (b j))
end
end GroundTheory.Heights₂.Heights


