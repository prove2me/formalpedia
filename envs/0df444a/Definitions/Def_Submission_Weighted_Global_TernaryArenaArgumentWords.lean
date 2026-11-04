-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaArgumentWords
-- name    : Submission_Weighted_Global_TernaryArenaArgumentWords
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T16:41:34.873206+00:00
-- url     : https://prove2.me/theorems/6a67b2f2-6883-4094-9498-021040c5c118
-- title:
--   Ternary Arena Argument Words
-- statement:
--   Definitions and structural lemmas for Ternary Arena Argument Words, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaArgumentWords.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaMomentResources
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaArgumentWords
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaLayout WeightedGlobalCoverGoodMaps
open WeightedGlobalLocalParameters TernaryJointType
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
def scalars (m p F r count : ℕ) : List ℕ :=
  [r,p,4^fixedLength m,F,p^r,nb m r,2*N m r,cut m r,r*alphaRank m,
    2^(r*fixedAlpha m 2),F^r,(N m r+1)*nb m r,N m r*nb m r,4^(N m r),count,1]
def scalarControl (m p F r count : ℕ) : ℕ :=(scalars m p F r count).sum
end ThreeSum.WeightedGlobalArenaArgumentWords


