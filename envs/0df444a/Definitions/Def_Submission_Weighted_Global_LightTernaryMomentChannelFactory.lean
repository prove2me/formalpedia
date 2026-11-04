-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryMomentChannelFactory
-- name    : Submission_Weighted_Global_LightTernaryMomentChannelFactory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:46:28.065189+00:00
-- url     : https://prove2.me/theorems/7b3e3652-9f3a-4198-b5ed-c8f58b5cc1b3
-- title:
--   Light Ternary Moment Channel Factory
-- statement:
--   Definitions and structural lemmas for Light Ternary Moment Channel Factory, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryMomentChannelFactory.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernarySourceCountWeightSeed
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentSourceProgram
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedGlobalMomentChannelFactory
open Light TernaryJointType TernaryWeightChannels
def leftWeights (k j : ℕ) (B : ℕ→ℤ) (i : ℕ) : ℤ := (k.choose j : ℤ)*(-(B i))^j
def rightWeights (k j : ℕ) (C : ℕ→ℤ) (i : ℕ) : ℤ := (C i)^(k-j)
def score {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (B C : ℕ→ℤ) (k j i : ℕ) : ℤ :=
  TernaryConvolution.factorial (S.front.Q i)*
    TernaryWeightedPhysicalSources.pairWeight
      (TernarySourceHostModel.channel S.left.records S.left.group (S.front.group i))
      (TernarySourceHostModel.channel S.right.records S.right.group (S.front.group i))
      (fun pair => S.front.E.word (S.left.key pair.2))
      (fun pair => S.front.E.word (S.right.key pair.2))
      (fun pair => leftWeights k j B pair.1) (fun pair => rightWeights k j C pair.1) (S.front.Q i)
def program {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (k j : ℕ) : Program :=
  LightWeightedGlobalMomentSourceProgram.program S.left.xs S.left.ys S.left.zs
    S.right.xs S.right.ys S.right.zs k j
def args {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (originalB originalC matrix : ℕ) : List ℤ :=
  LightTernaryMomentChannelStep.args originalB S.left.NL originalC S.right.NL
    S.left.weightBase S.right.weightBase matrix S.front.count S.front.dst S.argv
end ThreeSum.LightWeightedGlobalMomentChannelFactory


