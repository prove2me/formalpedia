-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaScoreScan
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaScoreScan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:14:28.648658+00:00
-- url     : https://prove2.me/theorems/54f48cbf-5782-4a50-8c9b-6a4929e6bb12
-- title:
--   TernaryArenaScoreScan
-- statement:
--   Definitions and structural lemmas for TernaryArenaScoreScan, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaScoreScan.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Theorems.Thm_Light_Ends_store
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_Reads_update

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaScoreScan
open LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
set_option maxHeartbeats 2000000
def Protected (I : Input) (x : ℕ) : Prop :=
  (x < addr I.free I.capacity 9 ∨ addr I.free I.capacity 13 ≤ x) ∧
  x < addr I.free I.capacity 16 ∧ x ≠ addr I.free I.capacity 1+104
def KeepInputs (I : Input) (μ ν : ℕ→ℤ) : Prop :=
  ∀x, Protected I x → ν x=μ x
def cell (I : Input) (channel seed : ℕ) : ℕ :=
  addr I.free I.capacity (9+channel)+seed
def store (I : Input) (i : ℕ) (v : Fin 4→ℤ) (μ : ℕ→ℤ) : ℕ→ℤ :=
  Function.update (Function.update (Function.update (Function.update μ
    (cell I 0 i) (v 0)) (cell I 1 i) (v 1)) (cell I 2 i) (v 2)) (cell I 3 i) (v 3)
def Scores (I : Input) (values : ℕ→Fin 4→ℤ) (n : ℕ) (μ : ℕ→ℤ) : Prop :=
  ∀i < n, ∀c : Fin 4, μ (cell I c i)=values i c
def Invariant (I : Input) (values : ℕ→Fin 4→ℤ) (μ : ℕ→ℤ) (n : ℕ) (ν : ℕ→ℤ) : Prop :=
  KeepInputs I μ ν ∧ Scores I values n ν
variable {p r : ℕ} [Fact p.Prime]
def values {I : Input} {A : Inputs} (D : Family (config p r I A 0)) (K i : ℕ) : Fin 4→ℤ :=
  ![D.flag i,D.scoreB i,D.scoreC i,D.scoreP K i]
end ThreeSum.WeightedGlobalArenaScoreScan
end
end WeightedCache3SUMRefinement_e1ae71d


