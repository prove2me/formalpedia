-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_DivisorFrames_NuDetMulSliceBBlockAction
-- name    : Development_AutomorphicArithmetic_DivisorFrames_NuDetMulSliceBBlockAction
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:16:39.54597+00:00
-- url     : https://prove2.me/theorems/04e2fa76-0daa-4e6f-9e05-c0d411838adc
-- title:
--   Nu Det Mul Slice BBlock Action
-- statement:
--   Definitions and structural lemmas for Nu Det Mul Slice BBlock Action, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DivisorFrames/NuDetMulSliceBBlockAction.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ScaledIntegerPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SplitThetaGridPathAvoidsOppositeCorner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise


