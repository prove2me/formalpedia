-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorDriverSyntax
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorDriverSyntax
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:18:41.336332+00:00
-- url     : https://prove2.me/theorems/5f515ef0-8727-4a71-ad99-a74c0b242011
-- title:
--   LightTernaryTensorDriverSyntax
-- statement:
--   Definitions and structural lemmas for LightTernaryTensorDriverSyntax, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryTensorDriverSyntax.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountHost
import Definitions.Def_Submission_ThreeSum_LightTernaryTaggedChannel
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotentialBatch
import Definitions.Def_Submission_ThreeSum_LightTernaryTensorScatter
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedGlobalTensorDriver
open Light
def countArgs : List Expr := (List.range 106).map (fun i => M (v 0 +' k i))
def body (pPowers pRow pStep pPotentialBatch : ℕ) : Stmt :=
  .set 15 (v 5 +' k 2) ;;
  .call pPowers [v 12,k 5,v 15] 17 ;;
  .set 16 (M (v 12 +' k 4)) ;;
  .for 18 (v 16) (
    .call pRow [k 4,v 15,v 18,v 12,k 0,k 1,v 11,k 4] 19 ;;
    .call pStep [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,
      M (v 11),M (v 11 +' k 1),M (v 11 +' k 2),M (v 11 +' k 3),v 18,v 16] 20) ;;
  .call pPotentialBatch [v 8,v 15,v 9,v 13,v 14] 0
def time (K J nLeft nRight wantedCount hostTime : ℕ) : ℕ :=
  powTableTime 5+(J+2)^4*(LightWeightRow.time 4 ((J+2)^4)+
    LightTernaryTaggedChannel.time nLeft+LightTernaryTaggedChannel.time nRight+
    hostTime+LightTernaryTensorScatter.time wantedCount+2000)+
    LightTernaryPairedPotentialBatch.time K (J+2) wantedCount+1000
end ThreeSum.LightWeightedGlobalTensorDriver
end
end WeightedCache3SUMRefinement_e1ae71d


