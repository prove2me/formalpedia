-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapMulLeftEqNormSmulStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapMulLeftEqNormSmulStatement
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:49:59.247102+00:00
-- url     : https://prove2.me/theorems/e0aa0de6-c318-471b-a4c1-eb9ddf9a33d7
-- title:
--   Map Mul Left Eq Norm Smul Statement
-- statement:
--   Definitions and structural lemmas for Map Mul Left Eq Norm Smul Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapMulLeftEqNormSmulStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapMulLeftEqNormSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
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


