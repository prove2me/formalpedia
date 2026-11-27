-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HilbertTensorTraceClassHasTraceProd
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_HilbertTensorTraceClassHasTraceProd
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-27T06:11:00.107812+00:00
-- url     : https://prove2.me/theorems/8f4c35a7-5b95-579a-8f2d-913d1d7bc82c
-- title:
--   Hilbert Tensor Trace Class Has Trace Prod
-- statement:
--   Definitions and structural lemmas for Hilbert Tensor Trace Class Has Trace Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HilbertTensorTraceClassHasTraceProd.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SplitHeightSummableExpNegAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousMultilinearMapExtHilbertBasisStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsHilbertSchmidtOrthonormalApplyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumTupleProdOfSummableNormComplexStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ContinuousLinearMap
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory
open GlobalTheory.OpTrace
end GlobalTheory


