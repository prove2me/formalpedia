-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilRepresentationPreservesL2Space
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilRepresentationPreservesL2Space
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T22:36:08.313435+00:00
-- url     : https://prove2.me/theorems/69d72630-504f-4846-a37a-cbefb6e94249
-- title:
--   Weil Representation Preserves L2 Space
-- statement:
--   Definitions and structural lemmas for Weil Representation Preserves L2 Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilRepresentationPreservesL2Space.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformTwiceEqPosSmulReflectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SiegelParabolicWeylElementGenerateUnitaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSelfDualBicharacterPairingOfSymmBilinFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralSqSiegelParabolicOperatorEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralFourSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianMatrixColumnPairingAlgebraicPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuadExtTopologyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped ENNReal NNReal
namespace GlobalTheory.KSp
end GlobalTheory.KSp


