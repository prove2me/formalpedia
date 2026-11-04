-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaTerminalReceipt
-- name    : Submission_Weighted_Global_TernaryArenaTerminalReceipt
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T01:58:22.420962+00:00
-- url     : https://prove2.me/theorems/8b46f6e3-53ae-4e56-96b8-908d7d635b03
-- title:
--   Ternary Arena Terminal Receipt
-- statement:
--   Definitions and structural lemmas for Ternary Arena Terminal Receipt, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTerminalReceipt.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhaseBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalMetadata
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPreparedMemory
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_ThreeSum_WeightedGlobalPreparedOriginals_metadata

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaTerminalReceipt
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalArenaSeedData WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open WeightedGlobalArenaSelectedSigned WeightedGlobalArenaSelectedTerminal WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 7000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
structure QueryReceipt (maps : Fin F→Weight m p) (τ cap r : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (μ : ℕ→ℤ) : Prop where
  metadata : WeightedGlobalArenaPostMemory.Metadata (r := r) maps τ I μ
  host : Seg μ (addr I.free I.capacity 1) (setup (r := r) maps τ cap Q I).argv
variable {K : ℕ}
end ThreeSum.WeightedGlobalArenaTerminalReceipt


