-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaScoreScan
-- name    : Submission_Weighted_Global_TernaryArenaScoreScan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T21:10:23.91549+00:00
-- url     : https://prove2.me/theorems/a42b5a71-694a-4935-a374-79ce62fcfc39
-- title:
--   Ternary Arena Score Scan
-- statement:
--   Definitions and structural lemmas for Ternary Arena Score Scan, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaScoreScan.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Theorems.Thm_Light_Ends_store
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update

set_option autoImplicit false
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


