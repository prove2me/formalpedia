-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapLinearEquivAddHaarLocalField
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapLinearEquivAddHaarLocalField
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:10:46.190961+00:00
-- url     : https://prove2.me/theorems/203b8889-d876-4e04-9cd7-6f332f55716e
-- title:
--   Map Linear Equiv Add Haar Local Field
-- statement:
--   Definitions and structural lemmas for Map Linear Equiv Add Haar Local Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapLinearEquivAddHaarLocalField.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped NNReal ENNReal
namespace GlobalTheory.KSp
end GlobalTheory.KSp


