-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaArgumentWords
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaArgumentWords
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:33:37.790193+00:00
-- url     : https://prove2.me/theorems/8bfff680-efe1-4557-be03-c7b69c6f7ad4
-- title:
--   TernaryArenaArgumentWords
-- statement:
--   Definitions and structural lemmas for TernaryArenaArgumentWords, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaArgumentWords.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaMomentResources
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


