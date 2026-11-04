-- Prove2me | Definitions.Def_Submission_Weighted_BankStageModel
-- name    : Submission_Weighted_BankStageModel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:40:58.378673+00:00
-- url     : https://prove2.me/theorems/1e234be4-9870-43d9-941a-a13431433637
-- title:
--   Bank Stage Model
-- statement:
--   Definitions and structural lemmas for Bank Stage Model, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStageModel.lean

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_TernaryQuery_update_below
import Theorems.Thm_WeightedCache_concrete_cost_mono
import Theorems.Thm_WeightedCache_cost_mono

set_option autoImplicit false
namespace ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000
structure Enumeration (N T n : ℕ) where
  word : ℕ→TritWord N
  mem : ∀ j<n, WeightedCache.cost ![0,512,1025] (word j)≤T
  complete : ∀ R : TritWord N, WeightedCache.cost ![0,512,1025] R≤T → ∃ j<n, word j=R
def lowerWord {N : ℕ} (R : TritWord N) (i : Fin N) (e : Fin 3) : TritWord N :=
  Function.update R i (min e (R i))
theorem lowerWord_below {N : ℕ} (R : TritWord N) (i : Fin N) (e : Fin 3) :
    Below (lowerWord R i e) R := update_below R i _ (min_le_right _ _)
noncomputable def index {N T n : ℕ} (E : Enumeration N T n) (i : Fin N)
    (e : Fin 3) (j : ℕ) : ℕ :=
  if hj : j<n then Classical.choose (E.complete (lowerWord (E.word j) i e)
    ((WeightedCache.cost_mono WeightedCache.concrete_cost_mono (lowerWord_below (E.word j) i e)).trans (E.mem j hj))) else 0
def forwardStage {N : ℕ} (K : ℕ) (F : TritWord N→ℤ) : TritWord N→ℤ :=
  runZeta (coords N K) F
end ThreeSum.WeightedBankStageModel


