-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryFastProgramResources
-- name    : Submission_Weighted_Global_TernaryFastProgramResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T17:48:38.92689+00:00
-- url     : https://prove2.me/theorems/73d8d2c0-e81e-4258-b469-7eb07fa05169
-- title:
--   Ternary Fast Program Resources
-- statement:
--   Definitions and structural lemmas for Ternary Fast Program Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramResources.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_Submission_ThreeSum_ThreeSumColorDriverResources
set_option autoImplicit false
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


