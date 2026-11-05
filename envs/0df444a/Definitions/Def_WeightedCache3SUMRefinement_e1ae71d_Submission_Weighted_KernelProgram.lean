-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_KernelProgram
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_KernelProgram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:28:54.663039+00:00
-- url     : https://prove2.me/theorems/b6e74514-071a-4ab7-8efd-e28a019f1ba7
-- title:
--   KernelProgram
-- statement:
--   Definitions and structural lemmas for KernelProgram, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/KernelProgram.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearSourceWords
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankStages
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankCanonical
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightNearEnumerationMain
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenPhysical
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearSetup
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedKernel
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.WeightedPhysicalEuler
open ThreeSum.WeightedBankStageModel ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits}
def program : Program :=
  [LightWeightedNearSource.body 1 2 3,
   LightTernaryRankTable.body 4,
   LightWeightedEulerMetadata.body 5,
   LightTernaryEulerMemo.body 6,
   LightTernaryRank.body 7,
   LightWeightedPredecessorTable.body 8 7,
   LightTernaryEulerScan.body 9,
   LightTernaryCodes.digitBody 10,
   LightWeightedPredecessor.body 7 11 10 12 13,
   LightTernaryEulerRow.fillBody 14,
   LightMaskErase.body 10,
   LightTernaryCodes.zeroBody 10,
   LightWeightedCost.body 7,
   LightBandLookup.searchBody 13,
   LightTernaryEulerRow.body 15 16,
   LightTernaryWeightedSum.body,
   LightTernaryDivide.body 17,
   LightOutputDecodeDivide.body,
   LightWeightedBankSweep.body 19,
   LightWeightedBankCoordinate.body 20 21,
   LightTernaryMetadata.body 11 7 10,
   LightTernaryPass.body 22,
   LightTernaryLookup.body 13 23,
   LightTernaryCell.zetaBody,
   LightWeightedBankSweep.body 25,
   LightWeightedBankCoordinate.body 20 26,
   LightTernaryInversePass.body 27,
   LightTernaryLookup.body 13 28,
   LightTernaryCell.inverseBody,
   LightCacheEnumeration.body 29,
   powTableBody,
   LightWeightedNearEnumeration.body 32,
   LightWeightedNearEnumeration.branchBody 31,
   LightWeightedFrozenQuery.body 33 34 7 11 10,
   LightTernaryQueryLookup.body 13,
   LightTernaryProduct.body,
   LightWeightedNearDigits.body 7,
   LightWeightedNearSetup.body 30 36 31]
end ThreeSum.WeightedKernel
end
end WeightedCache3SUMRefinement_e1ae71d


