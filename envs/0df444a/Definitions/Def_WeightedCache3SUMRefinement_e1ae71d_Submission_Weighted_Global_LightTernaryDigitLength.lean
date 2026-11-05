-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDigitLength
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDigitLength
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:16:03.048859+00:00
-- url     : https://prove2.me/theorems/6a96a33d-e13c-4f4a-8c7f-4d951cbdbdf9
-- title:
--   LightTernaryDigitLength
-- statement:
--   Definitions and structural lemmas for LightTernaryDigitLength, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryDigitLength.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedGlobalDigitLength
open Light WeightedGlobalSignedPadding
def clogBody : Stmt :=
  .set 2 (k 0) ;;
  .set 3 (k 1) ;;
  .while (v 3 <' v 0) (
    .set 3 (v 3 *' v 1) ;;
    .set 2 (v 2 +' k 1)) ;;
  .set 0 (v 2)
def clogTime (b x : ℕ) : ℕ := 20*Nat.clog b x+20
def word (b x : ℕ) : ℕ := b*x+b+x+8
variable {lim : Limits} {P : Program} {d : ℕ}
def body (pClog : ℕ) : Stmt :=
  .set 3 (k 4 *' v 0 +' k 1) ;;
  .call pClog [v 3,v 1] 4 ;;
  .set 0 (v 4 +' v 2 +' k 1)
def time (b U : ℕ) : ℕ := clogTime b (4*U+1)+60
def program : Program := [body 1,clogBody]
end ThreeSum.LightWeightedGlobalDigitLength
end WeightedCache3SUMRefinement_e1ae71d


