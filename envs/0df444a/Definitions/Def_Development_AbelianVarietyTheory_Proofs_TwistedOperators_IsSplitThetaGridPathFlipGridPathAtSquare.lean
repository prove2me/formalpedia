-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSplitThetaGridPathFlipGridPathAtSquare
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSplitThetaGridPathFlipGridPathAtSquare
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:45.422459+00:00
-- url     : https://prove2.me/theorems/01c22268-4925-4d80-9d0a-88fb101ed034
-- title:
--   Is Split Theta Grid Path Flip Grid Path At Square
-- statement:
--   Definitions and structural lemmas for Is Split Theta Grid Path Flip Grid Path At Square, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSplitThetaGridPathFlipGridPathAtSquare.lean

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
open GlobalTheory.SplitFlip
namespace GlobalTheory.FlipPathPairwise
def srcDiff (e : Edge) : ℤ := (e.src.1 : ℤ) - e.src.2
end GlobalTheory.FlipPathPairwise


