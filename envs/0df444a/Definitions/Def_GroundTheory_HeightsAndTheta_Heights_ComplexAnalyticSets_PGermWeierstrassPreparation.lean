-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermWeierstrassPreparation
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermWeierstrassPreparation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:02.209648+00:00
-- url     : https://prove2.me/theorems/7026cbf4-7123-4fc7-b76b-22d74f327ccf
-- title:
--   PGerm Weierstrass Preparation
-- statement:
--   Definitions and structural lemmas for PGerm Weierstrass Preparation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermWeierstrassPreparation.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCircleArgumentPrinciple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPowerSumsEsymmAnalytic
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
open Topology Filter Metric Complex Real
noncomputable section
def pointWithLastCLM (σ : Type) : ((σ → ℂ) × ℂ) →L[ℂ] (Option σ → ℂ) :=
  ContinuousLinearMap.pi fun o => match o with
    | none => ContinuousLinearMap.snd ℂ (σ → ℂ) ℂ
    | some i => (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℂ (σ → ℂ) ℂ)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


