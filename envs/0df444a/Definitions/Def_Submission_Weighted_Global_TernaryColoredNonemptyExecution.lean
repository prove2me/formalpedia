-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredNonemptyExecution
-- name    : Submission_Weighted_Global_TernaryColoredNonemptyExecution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T04:23:05.937807+00:00
-- url     : https://prove2.me/theorems/76820285-01b6-4452-8a25-fa6e4a3bacff
-- title:
--   Ternary Colored Nonempty Execution
-- statement:
--   Definitions and structural lemmas for Ternary Colored Nonempty Execution, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredNonemptyExecution.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinishCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPreparationFields
import Definitions.Def_Submission_Weighted_Global_TernaryColoredInitializationResources
import Definitions.Def_Submission_Weighted_Global_TernaryColoredProgramIdentity
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_selected
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedCollisions_selected
import Theorems.Thm_ThreeSum_WeightedGlobalColoredConcreteFinalCall_call
import Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopCall_call

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredNonemptyExecution
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalArenaLayout WeightedGlobalLocalParameters
open LightWeightedGlobalColoredSolver LightWeightedGlobalColoredInitializationProof
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}
def tail (P : Profile κ) : Stmt :=
  .call 249 (loopArgs P.m P.F P.p (fixedAlpha P.m 2) (WeightedGlobalArenaSourceSetup.alphaRank P.m)
    (TernaryCodeSemantics.address P.output.val) (4^fixedLength P.m) (P.p^(2*P.K)) P.drift P.scale) 12 ;;
  .set 13 (k (fixedLength P.m) *' H 15) ;; .set 14 (k 2 *' v 13) ;;
  .call (252+WeightedGlobalExecutable.reportingMain (p:=P.p) P.K) postArgs 0
def postTime (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ→ℤ)
    [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))] :=
  LightWeightedGlobalPreparedPostSelection.time
    (WeightedGlobalArenaSourceSetup.setup (r:=rounds P n) P.maps P.threshold P.cap P.output
      (WeightedGlobalColoredFinalReady.selected P n free menu c A B C initial)) P.H
    (WeightedGlobalColoredFinalReady.cleanup P n free A B C)
    (WeightedGlobalColoredTerminalReceipt.keysB P n free menu c A B C initial)
    (WeightedGlobalColoredTerminalReceipt.keysC P n free menu c A B C initial)
end ThreeSum.WeightedGlobalColoredNonemptyExecution


