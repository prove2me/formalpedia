-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankStages
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankStages
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:11:58.38808+00:00
-- url     : https://prove2.me/theorems/27c36a08-4a50-497a-a2e9-3b4b5321f0ec
-- title:
--   BankStages
-- statement:
--   Definitions and structural lemmas for BankStages, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankStages.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankSweep
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end WeightedCache3SUMRefinement_e1ae71d


