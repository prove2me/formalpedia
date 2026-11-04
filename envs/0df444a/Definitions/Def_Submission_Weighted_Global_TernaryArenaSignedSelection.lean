-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaSignedSelection
-- name    : Submission_Weighted_Global_TernaryArenaSignedSelection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:54:47.735257+00:00
-- url     : https://prove2.me/theorems/9e0da839-7272-4207-925c-2807190c0161
-- title:
--   Ternary Arena Signed Selection
-- statement:
--   Definitions and structural lemmas for Ternary Arena Signed Selection, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSignedSelection.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_Candidate_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_SpanGuard_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSignedSelection
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedSigned WeightedGlobalArenaBudgetExistence WeightedGlobalCoverGoodMaps
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
variable (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (K n radix nA : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (X B C : ℕ→ℤ) (catalog : ℕ→ℕ→ℕ→ℕ)
def initialBudget : ℕ := LightTernaryInitialBudgets.initial K radix n A.J (nA*2^A.J)
def state (r : ℕ) : State (p := p) A :=
  run maps τ cap U V scoreBound Q (base I A.J nA) A radix K n (initialBudget A K n radix nA) e ℓ
    (left U radix A.J B) (right U radix A.J C) (requester U radix A.J X) catalog r
end ThreeSum.WeightedGlobalArenaSignedSelection


