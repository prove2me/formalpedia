-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFastProgramResources
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFastProgramResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T14:52:54.472547+00:00
-- url     : https://prove2.me/theorems/0e976c91-4188-4d52-b11f-b7dc29c78a89
-- title:
--   TernaryFastProgramResources
-- statement:
--   Definitions and structural lemmas for TernaryFastProgramResources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryFastProgramResources.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_Submission_ThreeSum_ThreeSumColorDriverResources
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalFastProgramResources
open Light LightWeightedGlobalFastProgram LightWeightedGlobalFastProgramProof
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
def need (M b p K κ : ℕ) (colorNeed : ℕ→ℕ→Need) (n U : ℕ) : Need :=
  let g := WeightedGlobalGlobalPreludeResources.need M b p K κ n U
  let c := ThreeSumColorDriverResources.need colorNeed n U
  ⟨g.word+c.word,g.cells+c.cells,g.depth+c.depth+2⟩
end ThreeSum.WeightedGlobalFastProgramResources
end
end WeightedCache3SUMRefinement_e1ae71d


