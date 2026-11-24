-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermsNoetherian
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermsNoetherian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:52.72728+00:00
-- url     : https://prove2.me/theorems/017f6563-43af-42c3-bfdc-3dfc295374f5
-- title:
--   St Analytic Germs Noetherian
-- statement:
--   Definitions and structural lemmas for St Analytic Germs Noetherian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StAnalyticGermsNoetherian.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
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
def AnalyticGermsNoetherian.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ), IsNoetherianRing (holGerms w)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


