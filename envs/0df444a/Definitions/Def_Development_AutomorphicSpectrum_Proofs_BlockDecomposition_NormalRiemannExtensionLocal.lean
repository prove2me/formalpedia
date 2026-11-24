-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormalRiemannExtensionLocal
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormalRiemannExtensionLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:19.096286+00:00
-- url     : https://prove2.me/theorems/c1a95e63-a7d9-4f64-99a3-9dbbf0b52be4
-- title:
--   Normal Riemann Extension Local
-- statement:
--   Definitions and structural lemmas for Normal Riemann Extension Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormalRiemannExtensionLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalRiemannExtensionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalUniversalDenominator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalBoundedQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GlobalTheory.CompanionTheory.Ar.Branch
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets MvPolynomial Topology Filter Metric
end GlobalTheory.CompanionTheory.Ar.Branch


