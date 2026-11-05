-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorFactory
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorFactory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:49:05.378005+00:00
-- url     : https://prove2.me/theorems/556db0cc-1ae3-4a4b-bf84-ed99af60ff11
-- title:
--   LightTernaryTensorFactory
-- statement:
--   Definitions and structural lemmas for LightTernaryTensorFactory, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryTensorFactory.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorDriverProof
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotentialBatchFinal
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySourceCountWeightSeed
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_main
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_main
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.main
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.main
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedGlobalTensorFactory
open Light TernaryJointType
abbrev program {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (K : ℕ) : Program :=
  LightWeightedGlobalTensorDriver.program S.left.xs S.left.ys S.left.zs S.right.xs S.right.ys S.right.zs K
def leftWeights (J q : ℕ) (L : ℕ→ℕ→ℤ) (i : ℕ) : ℤ :=
  L i (LightWeightedGlobalTensorDriver.digit J q 0)*L i (LightWeightedGlobalTensorDriver.digit J q 1)
def rightWeights (J q : ℕ) (R : ℕ→ℕ→ℤ) (i : ℕ) : ℤ :=
  R i (LightWeightedGlobalTensorDriver.digit J q 2)*R i (LightWeightedGlobalTensorDriver.digit J q 3)
def score {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (J : ℕ) (L R : ℕ→ℕ→ℤ) (wanted q : ℕ) : ℤ :=
  TernaryConvolution.factorial (S.front.Q wanted)*
    TernaryWeightedPhysicalSources.pairWeight
      (TernarySourceHostModel.channel S.left.records S.left.group (S.front.group wanted))
      (TernarySourceHostModel.channel S.right.records S.right.group (S.front.group wanted))
      (fun pair => S.front.E.word (S.left.key pair.2))
      (fun pair => S.front.E.word (S.right.key pair.2))
      (fun pair => leftWeights J q L pair.1) (fun pair => rightWeights J q R pair.1) (S.front.Q wanted)
def extras (K : ℕ) : Program :=
  LightTernaryTaggedChannel.program.map (ReportingHostRelocation.relocate 135)++
  LightWeightRow.program.map (ReportingHostRelocation.relocate 138)++
  (LightTernaryPairedPotential.program K).map (ReportingHostRelocation.relocate 141)++
  [LightTernaryPairedPotentialBatch.body 141,LightTernaryTensorScatter.body,
    LightWeightedGlobalQuarticStep.body 135 134 148,LightWeightedGlobalTensorDriver.body 142 138 149 147]
structure Procs {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (K : ℕ) : Prop where
  main : (program S K)[150]?=some (LightWeightedGlobalTensorDriver.body 142 138 149 147)
  powers : (program S K)[142]?=some powTableBody
  row : (program S K)[138]?=some (LightWeightRow.body 139)
  digit : (program S K)[139]?=some (LightRadixDigit.body 140)
  divide : (program S K)[140]?=some LightSmallDivide.body
  channel : (program S K)[135]?=some (LightTernaryTaggedChannel.body 136 137)
  offset : (program S K)[136]?=some LightTernaryTaggedChannel.offsetBody
  product : (program S K)[137]?=some LightTernaryProductChannel.body
  scatter : (program S K)[148]?=some LightTernaryTensorScatter.body
  step : (program S K)[149]?=some (LightWeightedGlobalQuarticStep.body 135 134 148)
  batch : (program S K)[147]?=some (LightTernaryPairedPotentialBatch.body 141)
  potential : (program S K)[141]?=some (LightTernaryPairedPotential.body K 142 143 146)
  potentialRow : (program S K)[143]?=some (LightWeightRow.body 144)
  potentialDigit : (program S K)[144]?=some (LightRadixDigit.body 145)
  potentialDivide : (program S K)[145]?=some LightSmallDivide.body
  polynomial : (program S K)[146]?=some (LightTernaryPairedPolynomial.body K)
end ThreeSum.LightWeightedGlobalTensorFactory
end
end WeightedCache3SUMRefinement_e1ae71d


