-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermProjectionStep
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermProjectionStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:58.167189+00:00
-- url     : https://prove2.me/theorems/365b087f-69b8-4f72-a7e9-00487c103028
-- title:
--   PPrime Germ Projection Step
-- statement:
--   Definitions and structural lemmas for PPrime Germ Projection Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeGermProjectionStep.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermProjectionStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermGeneralCoordinates
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
noncomputable section
def affineGerm {σ : Type} [Fintype σ] (w : σ → ℂ) (L : (σ → ℂ) →L[ℂ] ℂ) (c : ℂ) : holGerms w :=
  ⟨↑(fun z : σ → ℂ => L z + c), fun z => L z + c, (L.analyticAt w).add analyticAt_const, rfl⟩
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


