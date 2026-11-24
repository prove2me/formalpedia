-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SplitThetaGridPathAvoidsOppositeCorner
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_SplitThetaGridPathAvoidsOppositeCorner
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:35.379528+00:00
-- url     : https://prove2.me/theorems/fa565104-5cb3-485d-b67c-0746a4f6c30a
-- title:
--   Split Theta Grid Path Avoids Opposite Corner
-- statement:
--   Definitions and structural lemmas for Split Theta Grid Path Avoids Opposite Corner, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SplitThetaGridPathAvoidsOppositeCorner.lean

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
def vertexDiff (X : ℕ × ℕ) : ℤ := (X.1 : ℤ) - X.2
end GlobalTheory.SplitFlip


