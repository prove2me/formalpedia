-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeTensorScore
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeTensorScore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:17:12.606364+00:00
-- url     : https://prove2.me/theorems/0c2e8c0c-6458-406e-b415-6d80a00a668c
-- title:
--   TernaryNativeTensorScore
-- statement:
--   Definitions and structural lemmas for TernaryNativeTensorScore, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeTensorScore.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairMoments
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


