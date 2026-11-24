-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatMinorSupport
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatMinorSupport
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:48:21.326413+00:00
-- url     : https://prove2.me/theorems/86920575-63dd-456d-a68a-40d980c4fab2
-- title:
--   Schwartz Bruhat Minor Support
-- statement:
--   Definitions and structural lemmas for Schwartz Bruhat Minor Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatMinorSupport.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartStackDecompositionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartBoundedCoefficientsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartShearInvarianceStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
namespace GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.LocMod.Inhab ValuativeRel
end GlobalTheory.RankChart


