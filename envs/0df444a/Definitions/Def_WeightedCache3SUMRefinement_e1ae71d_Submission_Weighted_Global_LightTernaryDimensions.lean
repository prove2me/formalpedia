-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensions
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:22:19.876843+00:00
-- url     : https://prove2.me/theorems/7ffbe2b9-b83e-49e6-806f-5177e3534bc2
-- title:
--   LightTernaryDimensions
-- statement:
--   Definitions and structural lemmas for LightTernaryDimensions, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryDimensions.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDigitLength
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedGlobalDimensions
open Light WeightedGlobalSignedPadding TernaryExtensionEncoding
set_option maxHeartbeats 3000000
def body (M b p K : ℕ) : Stmt :=
  .set 3 (v 0 *' v 0) ;;
  .call 1 [v 3,k M] 4 ;;
  .call 2 [v 1,k b,v 4] 5 ;;
  .set 8 (k (8*p^(4*K)) *' (v 5 +' k 3)) ;;
  .call 1 [v 8,k p] 6 ;;
  .call 3 [k p,v 6] 7 ;;
  .store (v 2) (v 4) ;;
  .store (v 2 +' k 1) (v 5) ;;
  .store (v 2 +' k 2) (v 6) ;;
  .store (v 2 +' k 3) (v 7) ;;
  .set 0 (v 7)
def program (M b p K : ℕ) : Program :=
  [body M b p K,LightWeightedGlobalDigitLength.clogBody,
    LightWeightedGlobalDigitLength.body 1,LightNatPower.body]
def r (M n : ℕ) := Nat.clog M (n^2)
def J (M b n U : ℕ) := paddedLength b U (r M n)
def dim (M b p K n U : ℕ) := menuDegree p (J M b n U+2) K
def word (M b p K n U : ℕ) : ℕ :=
  2*(LightWeightedGlobalDigitLength.word M (n^2)+LightWeightedGlobalDigitLength.word b (4*U+1)+
    LightWeightedGlobalDigitLength.word p (8*(J M b n U+3)*p^(4*K))+
    p^(dim M b p K n U)+r M n+J M b n U+dim M b p K n U+100)
def time (M b p K n U : ℕ) : ℕ :=
  LightWeightedGlobalDigitLength.clogTime M (n^2)+LightWeightedGlobalDigitLength.time b U+
    LightWeightedGlobalDigitLength.clogTime p (8*(J M b n U+3)*p^(4*K))+
    LightNatPower.time (dim M b p K n U)+250
variable {lim : Limits} {depth : ℕ}
end ThreeSum.LightWeightedGlobalDimensions
end WeightedCache3SUMRefinement_e1ae71d


