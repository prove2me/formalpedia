-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredProgramIdentity
-- name    : Submission_Weighted_Global_TernaryColoredProgramIdentity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:06:20.6673+00:00
-- url     : https://prove2.me/theorems/89bb7807-add6-419e-ba47-6e9214b9dbed
-- title:
--   Ternary Colored Program Identity
-- statement:
--   Definitions and structural lemmas for Ternary Colored Program Identity, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredProgramIdentity.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixCall
import Theorems.Thm_ThreeSum_SharedReportingBankData_Tables_reporting
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredProgramIdentity
open Light WeightedGlobalConcreteProfile WeightedGlobalArenaSourceSetup
variable {κ : ℕ}
def libraries (P : Profile κ) : Program :=
  LightWeightedGlobalColoredSolver.libraries P.radix P.allocation.D P.allocation.E P.K P.radix
    (P.p^(2*P.K)) P.drift P.scale P.p (4^WeightedGlobalLocalParameters.fixedLength P.m) P.F
    (WeightedGlobalGoodOutputCatalog.raws P.maps P.threshold) (WeightedGlobalGoodOutputCatalog.wordCodes P.maps P.threshold)
    (WeightedGlobalGoodOutputCatalog.mapCodes P.maps P.threshold)
    ((WeightedGlobalExecutable.leftRecords P.maps P.cap).map (TernaryCanonicalDictionaries.native false P.maps))
    ((WeightedGlobalExecutable.leftRecords P.maps P.cap).map TernaryCanonicalDictionaries.wordCode)
    ((WeightedGlobalExecutable.leftRecords P.maps P.cap).map TernaryCanonicalDictionaries.mapCode)
    ((WeightedGlobalExecutable.rightRecords P.maps P.cap).map (TernaryCanonicalDictionaries.native true P.maps))
    ((WeightedGlobalExecutable.rightRecords P.maps P.cap).map TernaryCanonicalDictionaries.wordCode)
    ((WeightedGlobalExecutable.rightRecords P.maps P.cap).map TernaryCanonicalDictionaries.mapCode)
def driver (P : Profile κ) : Stmt :=
  LightWeightedGlobalColoredSolver.body (252+WeightedGlobalExecutable.reportingMain (p:=P.p) P.K)
    P.m P.F P.p (WeightedGlobalLocalParameters.fixedAlpha P.m 2) (alphaRank P.m)
    (TernaryCodeSemantics.address P.output.val) (4^WeightedGlobalLocalParameters.fixedLength P.m)
    (P.p^(2*P.K)) P.drift P.scale (WeightedGlobalLocalParameters.fixedLength P.m)
def suffix (P : Profile κ) : Program :=
  (WeightedGlobalExecutable.reporting P.maps P.cap P.K).map (ReportingHostRelocation.relocate 252)++[driver P]
end ThreeSum.WeightedGlobalColoredProgramIdentity


