-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryBankStages
-- name    : Submission_ThreeSum_LightTernaryBankStages
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:51:38.517469+00:00
-- url     : https://prove2.me/theorems/1f887b49-ffb9-4c0b-8d35-10f51dfb1eeb
-- title:
--   Light Ternary Bank Stages
-- statement:
--   Definitions and structural lemmas for Light Ternary Bank Stages, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankStages.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryBankSweep
set_option autoImplicit false
namespace ThreeSum.LightTernaryBankStages
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}
def program (inverse : Bool) : Program :=
  [LightTernaryBankSweep.body 1,
   LightTernaryBankCoordinate.body 2 6,
   LightTernaryMetadata.body 3 4 5,
   LightTernaryCodes.zeroBody 5,
   LightTernaryCodes.digitBody 5,
   LightMaskErase.body 5,
   if inverse then LightTernaryInversePass.body 7 else LightTernaryPass.body 7,
   LightTernaryLookup.body 8 9,
   LightBandLookup.searchBody 8,
   if inverse then LightTernaryCell.inverseBody else LightTernaryCell.zetaBody]
end ThreeSum.LightTernaryBankStages


