-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteFibreCentredEquation
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteFibreCentredEquation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:30.9988+00:00
-- url     : https://prove2.me/theorems/a4642b79-c069-4e01-8d19-caeea8632608
-- title:
--   PFinite Fibre Centred Equation
-- statement:
--   Definitions and structural lemmas for PFinite Fibre Centred Equation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteFibreCentredEquation.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreCentredEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
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
open Topology Filter Polynomial
noncomputable def FiniteFibreCentredEquation.centredPoly (a : ℂ) {k : ℕ} (c : Fin k → ℂ) : ℂ[X] :=
  (X - C a) ^ k + ∑ j : Fin k, C (c j) * (X - C a) ^ (j : ℕ)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


