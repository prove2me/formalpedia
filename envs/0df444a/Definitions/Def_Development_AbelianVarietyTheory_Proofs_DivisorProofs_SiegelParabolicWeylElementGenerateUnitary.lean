-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SiegelParabolicWeylElementGenerateUnitary
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SiegelParabolicWeylElementGenerateUnitary
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:59:15.418056+00:00
-- url     : https://prove2.me/theorems/01d24d2a-964b-456c-a355-9d90fc6211b0
-- title:
--   Siegel Parabolic Weyl Element Generate Unitary
-- statement:
--   Definitions and structural lemmas for Siegel Parabolic Weyl Element Generate Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelParabolicWeylElementGenerateUnitary.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsTranslateInCellStatement
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
namespace GlobalTheory.KSp
end GlobalTheory.KSp


