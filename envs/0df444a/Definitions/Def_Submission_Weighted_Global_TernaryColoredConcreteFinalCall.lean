-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredConcreteFinalCall
-- name    : Submission_Weighted_Global_TernaryColoredConcreteFinalCall
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:26:40.050399+00:00
-- url     : https://prove2.me/theorems/1ba715b5-0a0e-445d-a9ab-980a0f3b8396
-- title:
--   Ternary Colored Concrete Final Call
-- statement:
--   Definitions and structural lemmas for Ternary Colored Concrete Final Call, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredConcreteFinalCall.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalReady
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredConcreteFinalCall
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalColoredTerminalReceipt WeightedGlobalColoredFinalReady
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}
def pre (P : Profile κ) : Program :=
  LightWeightedGlobalColoredSolver.libraries P.radix P.allocation.D P.allocation.E P.K P.radix
    (P.p^(2*P.K)) P.drift P.scale P.p (4^fixedLength P.m) P.F
    (WeightedGlobalGoodOutputCatalog.raws P.maps P.threshold)
    (WeightedGlobalGoodOutputCatalog.wordCodes P.maps P.threshold)
    (WeightedGlobalGoodOutputCatalog.mapCodes P.maps P.threshold)
    ((WeightedGlobalExecutable.leftRecords P.maps P.cap).map (TernaryCanonicalDictionaries.native false P.maps))
    ((WeightedGlobalExecutable.leftRecords P.maps P.cap).map TernaryCanonicalDictionaries.wordCode)
    ((WeightedGlobalExecutable.leftRecords P.maps P.cap).map TernaryCanonicalDictionaries.mapCode)
    ((WeightedGlobalExecutable.rightRecords P.maps P.cap).map (TernaryCanonicalDictionaries.native true P.maps))
    ((WeightedGlobalExecutable.rightRecords P.maps P.cap).map TernaryCanonicalDictionaries.wordCode)
    ((WeightedGlobalExecutable.rightRecords P.maps P.cap).map TernaryCanonicalDictionaries.mapCode)
def suffix (P : Profile κ) : Program :=
  [LightWeightedGlobalColoredSolver.body ((pre P).length+WeightedGlobalExecutable.reportingMain (p:=P.p) P.K)
    P.m P.F P.p (fixedAlpha P.m 2) (alphaRank P.m) (TernaryCodeSemantics.address P.output.val)
    (4^fixedLength P.m) (P.p^(2*P.K)) P.drift P.scale (fixedLength P.m)]
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ→ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
end ThreeSum.WeightedGlobalColoredConcreteFinalCall


