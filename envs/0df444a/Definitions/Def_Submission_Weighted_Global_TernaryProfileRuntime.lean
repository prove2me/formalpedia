-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryProfileRuntime
-- name    : Submission_Weighted_Global_TernaryProfileRuntime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:20:35.982005+00:00
-- url     : https://prove2.me/theorems/3e2892d8-0876-42cf-8469-6f24845e57f2
-- title:
--   Ternary Profile Runtime
-- statement:
--   Definitions and structural lemmas for Ternary Profile Runtime, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryProfileRuntime.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramBudget
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Theorems.Thm_Light_Meets_main
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_main
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_main
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFixedParameters_cutoff
attribute [local simp] ThreeSum.LightTernaryCountFrontend.main
attribute [local simp] ThreeSum.LightWeightedCountFrontend.main


set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalConcreteProfile.Profile
open Light StageBounds WeightedGlobalLocalParameters WeightedGlobalActualColoredRuntime
open WeightedGlobalActualPrefixRuntime WeightedGlobalOversizeOverhead Filter
open scoped Topology
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {κ : ℕ}
def wordD (P : Profile κ) : ℕ :=256*(P.allocation.D+1)
def colorTime (P : Profile κ) : ℕ→ℕ :=
  WeightedGlobalActualGlobalQueryRuntime.uniformTime P.K P.k 19 3 P.m P.F P.wordD
    P.allocation.E κ P.p P.H P.radix
def fastTime (P : Profile κ) (n : ℕ) : ℕ :=
  LightWeightedGlobalFastProgramProof.time P.M P.radix P.p P.K κ (P.colorTime n) n
def hybridProgram (P : Profile κ) : Program :=
  TernaryHybridCore.program P.program P.main κ P.cutoff
def hybridMain (P : Profile κ) : ℕ :=P.program.length+5
def hybridNeed (P : Profile κ) : ℕ→ℕ→Need :=
  TernaryHybridResources.need P.need κ P.cutoff
def hybridTime (P : Profile κ) : ℕ→ℕ→ℕ :=
  TernaryHybridCore.time P.fastTime κ P.cutoff
end ThreeSum.WeightedGlobalConcreteProfile.Profile


