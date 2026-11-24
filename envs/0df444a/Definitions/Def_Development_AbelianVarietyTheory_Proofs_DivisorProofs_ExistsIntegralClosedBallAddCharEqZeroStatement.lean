-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntegralClosedBallAddCharEqZeroStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntegralClosedBallAddCharEqZeroStatement
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T21:25:26.831061+00:00
-- url     : https://prove2.me/theorems/8a046cc1-2a91-46be-b84b-f47ef35dba48
-- title:
--   Exists Integral Closed Ball Add Char Eq Zero Statement
-- statement:
--   Definitions and structural lemmas for Exists Integral Closed Ball Add Char Eq Zero Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIntegralClosedBallAddCharEqZeroStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntegralClosedBallAddCharEqZero
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


