-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicFundamentalDomainSplit
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicFundamentalDomainSplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:07.513552+00:00
-- url     : https://prove2.me/theorems/55b2a0f1-ccce-4896-9607-5ecf0363db37
-- title:
--   Parabolic Fundamental Domain Split
-- statement:
--   Definitions and structural lemmas for Parabolic Fundamental Domain Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ParabolicFundamentalDomainSplit.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitHomeoApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteCovolumeUnimodular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise
namespace GlobalTheory.CompanionTheory.SplitExtLat
end GlobalTheory.CompanionTheory.SplitExtLat


