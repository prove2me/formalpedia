-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProjectionPushforward
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProjectionPushforward
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:20.816309+00:00
-- url     : https://prove2.me/theorems/a9472e49-6e1a-4271-81d8-080aeb9e1927
-- title:
--   Finite Projection Pushforward
-- statement:
--   Definitions and structural lemmas for Finite Projection Pushforward, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteProjectionPushforward.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionOpenAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
namespace GlobalTheory.CompanionTheory.ComplexSets.DiscCover
open Metric
end GlobalTheory.CompanionTheory.ComplexSets.DiscCover
namespace GlobalTheory.CompanionTheory.ComplexSets
open Metric DiscCover
end GlobalTheory.CompanionTheory.ComplexSets


