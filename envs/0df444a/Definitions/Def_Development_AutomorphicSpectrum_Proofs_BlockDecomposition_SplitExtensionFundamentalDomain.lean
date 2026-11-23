-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitExtensionFundamentalDomain
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitExtensionFundamentalDomain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:41:06.203951+00:00
-- url     : https://prove2.me/theorems/87380af4-912b-45b0-81da-3e3eb171e067
-- title:
--   Split Extension Fundamental Domain
-- statement:
--   Definitions and structural lemmas for Split Extension Fundamental Domain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SplitExtensionFundamentalDomain.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitHomeoApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicFundamentalDomainSplitStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModularCharacterTrivialFiniteCovolumeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicHaarDecompositionStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicQuotientMeasureStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicFundamentalDomainVolumeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicIntegralUnfoldingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicLeviIntegralFormulaStatement
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


