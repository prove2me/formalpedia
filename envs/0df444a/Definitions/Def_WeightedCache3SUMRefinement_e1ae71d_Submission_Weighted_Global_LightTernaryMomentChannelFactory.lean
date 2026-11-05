-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentChannelFactory
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentChannelFactory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:10:31.701598+00:00
-- url     : https://prove2.me/theorems/5636fb6b-68ac-4dbb-85ab-9e07c894e679
-- title:
--   LightTernaryMomentChannelFactory
-- statement:
--   Definitions and structural lemmas for LightTernaryMomentChannelFactory, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryMomentChannelFactory.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySourceCountWeightSeed
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentSourceProgram
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


