-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
-- name    : Submission_Weighted_Global_TernaryNativeTensorScore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:58:49.795524+00:00
-- url     : https://prove2.me/theorems/744ab04b-0cbb-4a7e-8b07-8b27b02bd9f3
-- title:
--   Ternary Native Tensor Score
-- statement:
--   Definitions and structural lemmas for Ternary Native Tensor Score, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeTensorScore.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalNativeTensorScore
open TernaryJointType WeightedGlobalNativePairMoments
open LightWeightedGlobalTensorFactory LightTernaryPairedPolynomial
open scoped BigOperators
set_option maxHeartbeats 1500000
def originalLeft {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (J : ℕ) (L : ℕ→ℕ→ℤ) (i : ℕ) (pair : Pair S i) (a : Fin (J+2)) : ℤ := L pair.val.1.1 a.val
def originalRight {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (J : ℕ) (R : ℕ→ℕ→ℤ) (i : ℕ) (pair : Pair S i) (a : Fin (J+2)) : ℤ := R pair.val.2.1 a.val
def pairedPotential {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (K J : ℕ) (L R : ℕ→ℕ→ℤ) : ℕ :=
  ∑ i : Fin S.front.count, ∑ e : Fin K→Pair S i.val,
    TernaryPairedPotential.rowWeight (Sum.elim
      (fun j => originalLeft S J L i.val (e j)) (fun j => originalRight S J R i.val (e j)))
end ThreeSum.WeightedGlobalNativeTensorScore


