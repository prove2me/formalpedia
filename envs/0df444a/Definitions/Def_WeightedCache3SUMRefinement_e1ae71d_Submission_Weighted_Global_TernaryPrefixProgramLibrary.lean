-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixProgramLibrary
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixProgramLibrary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:00:20.096285+00:00
-- url     : https://prove2.me/theorems/beade2b5-3106-47f5-989d-bd28d352a7cf
-- title:
--   TernaryPrefixProgramLibrary
-- statement:
--   Definitions and structural lemmas for TernaryPrefixProgramLibrary, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixProgramLibrary.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixLoop
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedGlobalPrefixLoop
open Light
set_option maxHeartbeats 5000000
def tail : Program :=
  LightWeightedGlobalPrefixSetup.allocatedProgram.map (ReportingHostRelocation.relocate 179)++
    LightTernaryInitialKeys.program.map (ReportingHostRelocation.relocate 185)++
    LightTernaryCommitKeys.program.map (ReportingHostRelocation.relocate 187)++
    LightTernaryCommitSpan.program.map (ReportingHostRelocation.relocate 189)++
    [LightTernaryRepeatWord.body,headerBody,stepBody,loopBody,initBody,LightTernaryBudgetStep.body,prepareBody]
structure Library (P : Program) : Prop where
  prefixMain : P[179]?=some (LightWeightedGlobalPrefixSetup.body 180 181)
  power : P[180]?=some LightNatPower.body
  setup : P[181]?=some (LightWeightedEnumerationSetup.body 182 183)
  powers : P[182]?=some powTableBody
  enumeration : P[183]?=some (LightCacheEnumeration.body 183)
  allocate : P[184]?=some (LightWeightedGlobalPrefixSetup.allocateBody 180 179)
  initialFill : P[185]?=some fillBody
  initialMain : P[186]?=some (ReportingHostRelocation.relocate 185 LightTernaryInitialKeys.body)
  commitCopy : P[187]?=some copyBody
  commitMain : P[188]?=some (ReportingHostRelocation.relocate 187 LightTernaryCommitKeys.body)
  spanCopy : P[189]?=some copyBody
  repeatWord : P[190]?=some LightTernaryRepeatWord.body
  header : P[191]?=some headerBody
  step : P[192]?=some stepBody
  loop : P[193]?=some loopBody
  initial : P[194]?=some initBody
  budget : P[195]?=some LightTernaryBudgetStep.body
  prepare : P[196]?=some prepareBody
end ThreeSum.LightWeightedGlobalPrefixLoop
end
end WeightedCache3SUMRefinement_e1ae71d


