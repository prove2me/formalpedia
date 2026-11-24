-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_DivisorFrames_FourierSumBlockTransposeInvEq
-- name    : Development_AutomorphicArithmetic_DivisorFrames_FourierSumBlockTransposeInvEq
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:52.491741+00:00
-- url     : https://prove2.me/theorems/a7214a55-dca1-4f7a-9f01-942f594b11e3
-- title:
--   Fourier Sum Block Transpose Inv Eq
-- statement:
--   Definitions and structural lemmas for Fourier Sum Block Transpose Inv Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DivisorFrames/FourierSumBlockTransposeInvEq.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ScaledIntegerPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLatSmulBlockLat
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
namespace UpperTheory.FourierBlockTranspose
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end UpperTheory.FourierBlockTranspose


