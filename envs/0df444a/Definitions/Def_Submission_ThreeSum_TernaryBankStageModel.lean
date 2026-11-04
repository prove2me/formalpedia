-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryBankStageModel
-- name    : Submission_ThreeSum_TernaryBankStageModel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:41:19.560492+00:00
-- url     : https://prove2.me/theorems/87e7d3cd-e117-48c4-9218-42212ffd8144
-- title:
--   Ternary Bank Stage Model
-- statement:
--   Definitions and structural lemmas for Ternary Bank Stage Model, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankStageModel.lean

import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_TernaryBank_rank_mono
import Theorems.Thm_ThreeSum_TernaryQuery_update_below

set_option autoImplicit false
namespace ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000
structure Enumeration (N T n : ℕ) where
  word : ℕ→TritWord N
  mem : ∀ j<n, rank (word j)≤T
  complete : ∀ R : TritWord N, rank R≤T → ∃ j<n, word j=R
def lowerWord {N : ℕ} (R : TritWord N) (i : Fin N) (e : Fin 3) : TritWord N :=
  Function.update R i (min e (R i))
theorem lowerWord_below {N : ℕ} (R : TritWord N) (i : Fin N) (e : Fin 3) :
    Below (lowerWord R i e) R := update_below R i _ (min_le_right _ _)
noncomputable def index {N T n : ℕ} (E : Enumeration N T n) (i : Fin N)
    (e : Fin 3) (j : ℕ) : ℕ :=
  if hj : j<n then Classical.choose (E.complete (lowerWord (E.word j) i e)
    ((rank_mono (lowerWord_below (E.word j) i e)).trans (E.mem j hj))) else 0
def forwardStage {N : ℕ} (K : ℕ) (F : TritWord N→ℤ) : TritWord N→ℤ :=
  runZeta (coords N K) F
end ThreeSum.TernaryBankStageModel


