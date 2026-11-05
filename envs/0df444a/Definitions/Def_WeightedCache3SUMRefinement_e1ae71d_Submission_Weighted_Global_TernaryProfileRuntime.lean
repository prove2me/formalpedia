-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryProfileRuntime
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryProfileRuntime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:27:59.798194+00:00
-- url     : https://prove2.me/theorems/42b41c4f-f602-4c4c-b826-286c96a9c078
-- title:
--   TernaryProfileRuntime
-- statement:
--   Definitions and structural lemmas for TernaryProfileRuntime, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryProfileRuntime.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFastProgramBudget
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Theorems.Thm_Light_Meets_main
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_main
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_main
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFixedParameters_cutoff
attribute [local simp] ThreeSum.LightTernaryCountFrontend.main
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.main


set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


