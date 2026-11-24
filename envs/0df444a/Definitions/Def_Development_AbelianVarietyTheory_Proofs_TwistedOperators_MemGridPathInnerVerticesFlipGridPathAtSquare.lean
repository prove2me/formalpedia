-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemGridPathInnerVerticesFlipGridPathAtSquare
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemGridPathInnerVerticesFlipGridPathAtSquare
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:34.469697+00:00
-- url     : https://prove2.me/theorems/7c66d111-944b-4753-9bd4-2e4dcbf29fc0
-- title:
--   Mem Grid Path Inner Vertices Flip Grid Path At Square
-- statement:
--   Definitions and structural lemmas for Mem Grid Path Inner Vertices Flip Grid Path At Square, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemGridPathInnerVerticesFlipGridPathAtSquare.lean

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
namespace GlobalTheory.SplitFlip
def pathInnerDiff (X : ℕ × ℕ) : ℤ := (X.1 : ℤ) - X.2
end GlobalTheory.SplitFlip


