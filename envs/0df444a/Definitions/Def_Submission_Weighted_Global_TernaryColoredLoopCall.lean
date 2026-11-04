-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopCall
-- name    : Submission_Weighted_Global_TernaryColoredLoopCall
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:35:31.850246+00:00
-- url     : https://prove2.me/theorems/e8e2a7db-590d-4a97-be75-31ec9e62848f
-- title:
--   Ternary Colored Loop Call
-- statement:
--   Definitions and structural lemmas for Ternary Colored Loop Call, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopCall.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSeedABI
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopABI
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopReady
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocationScalars
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopABI_values

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredLoopCall
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open LightWeightedGlobalColoredInitializationProof
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ→ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
def initValues : List ℤ :=
  let I:=input P n free A B C
  let AP:=arrays P n free menu A B C
  values n (n^κ) I.free AP.Bmatrix I.nB AP.Cmatrix I.nC AP.Omatrix I.requesterCount
    AP.positions AP.menu AP.J P.p (4^fixedLength P.m) P.F (q P n)
end ThreeSum.WeightedGlobalColoredLoopCall


