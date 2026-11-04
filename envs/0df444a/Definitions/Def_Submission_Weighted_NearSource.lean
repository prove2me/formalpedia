-- Prove2me | Definitions.Def_Submission_Weighted_NearSource
-- name    : Submission_Weighted_NearSource
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:57:26.023578+00:00
-- url     : https://prove2.me/theorems/67b1e7ec-706e-4045-bc5e-508ce76ecf12
-- title:
--   Near Source
-- statement:
--   Definitions and structural lemmas for Near Source, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearSource.lean

import Definitions.Def_Submission_Weighted_PhysicalEuler
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightWeightedNearSource
open Light ThreeSum.LightSubsetAddress
open ThreeSum.LightWeightedEulerMetadata
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
def body (pRanks pMetadata pMemo : ℕ) : Stmt :=
  .call pRanks [v 0,v 1,v 2,v 3,v 11] 17 ;;
  .call pMetadata [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 1,v 2,v 12,v 7,v 8,v 9,v 10] 17 ;;
  .call pMemo [v 0,v 2,v 10,v 10 +' v 0 *' v 2,v 11,v 12,v 13,v 13,v 14,v 15,v 16] 17 ;;
  .set 0 (k 0)
def time (N L rows stages V : ℕ) : ℕ := LightTernaryRankTable.time N rows+
  LightWeightedEulerMetadata.time N L rows+LightTernaryEulerMemo.time N rows stages V+500
def weights (N : ℕ) (codes active : ℕ → ℕ) (j i : ℕ) : ℕ :=
  LightWeightedPredecessor.weight N (lowAt N i) (highAt N i) (codes j) (active i)
def keys (N rows T bv vals : ℕ) (codes active : ℕ → ℕ) (bi ni : ℕ → ℕ → ℕ) (j i : ℕ) : ℕ :=
  LightWeightedPredecessor.key N (lowAt N i) (highAt N i) (codes j) T (active i) bv vals (bi i j) (ni i j)
def ranks (N : ℕ) (codes : ℕ → ℕ) (j : ℕ) : ℕ := LightTernaryRank.partialRank N (codes j) N
variable {lim : Limits} {P : Program}
end ThreeSum.LightWeightedNearSource


