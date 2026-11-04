-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryNearSource
-- name    : Submission_ThreeSum_LightTernaryNearSource
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:57:50.374877+00:00
-- url     : https://prove2.me/theorems/b466b3d7-2f57-4d57-88c8-e6088036a620
-- title:
--   Light Ternary Near Source
-- statement:
--   Definitions and structural lemmas for Light Ternary Near Source, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearSource.lean

import Definitions.Def_Submission_ThreeSum_TernaryPhysicalEuler
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightTernaryNearSource
open Light ThreeSum.LightSubsetAddress
open ThreeSum.LightTernaryEulerMetadata
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
def body (pRanks pMetadata pMemo : ℕ) : Stmt :=
  .call pRanks [v 0,v 1,v 2,v 3,v 11] 17 ;;
  .call pMetadata [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 1,v 2,v 12,v 7,v 8,v 9,v 10] 17 ;;
  .call pMemo [v 0,v 2,v 10,v 10 +' v 0 *' v 2,v 11,v 12,v 8,v 13,v 14,v 15,v 16] 17 ;;
  .set 0 (k 0)
def time (N L rows stages V : ℕ) : ℕ := LightTernaryRankTable.time N rows+
  LightTernaryEulerMetadata.time N L rows+LightTernaryEulerMemo.time N rows stages V+500
def weights (N : ℕ) (codes active : ℕ → ℕ) (j i : ℕ) : ℕ :=
  LightTernaryPredecessor.weight N (lowAt N i) (highAt N i) (codes j) (active i)
def keys (N rows T bv vals : ℕ) (codes active : ℕ → ℕ) (bi ni : ℕ → ℕ → ℕ) (j i : ℕ) : ℕ :=
  LightTernaryPredecessor.key N (lowAt N i) (highAt N i) (codes j) T (active i) bv vals (bi i j) (ni i j)
def ranks (N : ℕ) (codes : ℕ → ℕ) (j : ℕ) : ℕ := LightTernaryRank.partialRank N (codes j) N
variable {lim : Limits} {P : Program}
end ThreeSum.LightTernaryNearSource


