-- Prove2me | Definitions.Def_Submission_Weighted_BankStages
-- name    : Submission_Weighted_BankStages
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:49:33.026626+00:00
-- url     : https://prove2.me/theorems/ed2e28c1-83bb-4dee-b7e4-a89ee9f8a44a
-- title:
--   Bank Stages
-- statement:
--   Definitions and structural lemmas for Bank Stages, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStages.lean

import Definitions.Def_Submission_Weighted_BankSweep
set_option autoImplicit false
namespace ThreeSum.LightWeightedBankStages
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}
def program (inverse : Bool) : Program :=
  [LightWeightedBankSweep.body 1,
   LightWeightedBankCoordinate.body 2 6,
   LightTernaryMetadata.body 3 4 5,
   LightTernaryCodes.zeroBody 5,
   LightTernaryCodes.digitBody 5,
   LightMaskErase.body 5,
   if inverse then LightTernaryInversePass.body 7 else LightTernaryPass.body 7,
   LightTernaryLookup.body 8 9,
   LightBandLookup.searchBody 8,
   if inverse then LightTernaryCell.inverseBody else LightTernaryCell.zetaBody]
end ThreeSum.LightWeightedBankStages


