-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryQuarticStep
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryQuarticStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:33:23.614068+00:00
-- url     : https://prove2.me/theorems/4cc0039d-88a5-414b-b0e1-99b72defd32d
-- title:
--   LightTernaryQuarticStep
-- statement:
--   Definitions and structural lemmas for LightTernaryQuarticStep, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryQuarticStep.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorHeader
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedGlobalQuarticStep
open Light
set_option maxHeartbeats 2400000
def body (pChannel pCount pScatter : ℕ) : Stmt :=
  .call pChannel [v 1,v 2,v 5,v 11,v 12,v 6] 17 ;;
  .call pChannel [v 3,v 4,v 5,v 13,v 14,v 7] 18 ;;
  .call pCount LightWeightedGlobalTensorDriver.countArgs 19 ;;
  .call pScatter [v 10,v 8,v 9,v 16,v 15] 0
end ThreeSum.LightWeightedGlobalQuarticStep
end WeightedCache3SUMRefinement_e1ae71d


