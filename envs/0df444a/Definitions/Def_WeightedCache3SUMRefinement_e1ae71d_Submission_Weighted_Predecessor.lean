-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Predecessor
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Predecessor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:08:59.246149+00:00
-- url     : https://prove2.me/theorems/474f70d1-ef30-4a0b-ba81-25a29b481511
-- title:
--   Predecessor
-- statement:
--   Definitions and structural lemmas for Predecessor, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Predecessor.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightCost
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedPredecessor
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
open ThreeSum.TernaryEuler
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
def digit (N low high m : ℕ) : ℕ := LightTernaryCodes.digit (2*N) low high m
def code (N low high m : ℕ) : ℕ :=
  if digit N low high m=1 then LightTernaryCodes.zeroCode (2*N) low high m
  else LightTernaryCodes.oneCode (2*N) high m
def predCost (N low high m : ℕ) : ℕ :=
  LightWeightedCost.partialCost N (code N low high m) N
def key (N low high m T active bankVals nearVals bankIndex nearIndex : ℕ) : ℕ :=
  if active=0 ∨ digit N low high m=0 then bankVals
  else if predCost N low high m≤T then bankVals+bankIndex else nearVals+nearIndex
def weight (N low high m active : ℕ) : ℕ :=
  if active=0 then 0 else digit N low high m
def lowerBody (pZero pErase : ℕ) : Stmt :=
  .ite (v 14 =' k 1)
    (.call pZero [k 2 *' v 0,v 1,v 2,v 3,v 4] 15)
    (.call pErase [k 2 *' v 0,v 2,v 3,k 2 *' v 0,v 4] 15)
def tailBody (pRank pSearch : ℕ) : Stmt :=
  .call pRank [v 0,v 15,v 4] 16 ;;
  .ite (v 13 =' k 0) (.set 0 (v 7))
    (.ite (v 14 =' k 0) (.set 0 (v 7))
      (.ite (v 16 ≤' v 12)
        (.call pSearch [v 5,v 6,v 15,v 4,v 11,k 0] 17 ;;
          .set 0 (v 7 +' v 17 -' k 1))
        (.call pSearch [v 8,v 9,v 15,v 4,v 11,k 0] 17 ;;
          .set 0 (v 10 +' v 17 -' k 1))))
def body (pDigit pZero pErase pRank pSearch : ℕ) : Stmt :=
  .call pDigit [k 2 *' v 0,v 1,v 2,v 3,v 4] 14 ;;
  lowerBody pZero pErase ;; tailBody pRank pSearch
def time (N L : ℕ) : ℕ := LightTernaryCodes.digitTime (2*N)+
  LightTernaryCodes.zeroTime (2*N)+LightMaskErase.time (2*N)+
  LightWeightedCost.time N+LightBandLookup.searchTime L+500
variable {lim : Limits} {P : Program}
end ThreeSum.LightWeightedPredecessor
end WeightedCache3SUMRefinement_e1ae71d


