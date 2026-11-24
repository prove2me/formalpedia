-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlipGridPathAtSquareSplit
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlipGridPathAtSquareSplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:28.244497+00:00
-- url     : https://prove2.me/theorems/cc74a4bc-c637-4968-8324-234a81694ed7
-- title:
--   Flip Grid Path At Square Split
-- statement:
--   Definitions and structural lemmas for Flip Grid Path At Square Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlipGridPathAtSquareSplit.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.SplitFlip.PathSplit
open GlobalTheory.SplitFlip
def vdiff (X : ℕ × ℕ) : ℤ := (X.1 : ℤ) - X.2
end GlobalTheory.SplitFlip.PathSplit
namespace GlobalTheory.SplitFlip
open GlobalTheory.SplitFlip.PathSplit
end GlobalTheory.SplitFlip


