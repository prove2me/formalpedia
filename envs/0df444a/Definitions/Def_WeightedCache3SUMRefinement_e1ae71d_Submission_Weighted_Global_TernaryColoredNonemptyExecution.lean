-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredNonemptyExecution
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredNonemptyExecution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:21:46.433124+00:00
-- url     : https://prove2.me/theorems/abc9a3ff-0c1e-42d7-b40c-9588ec5a5c33
-- title:
--   TernaryColoredNonemptyExecution
-- statement:
--   Definitions and structural lemmas for TernaryColoredNonemptyExecution, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredNonemptyExecution.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopCall
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredFinishCall
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPreparationFields
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredInitializationResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredProgramIdentity
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_selected
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSelectedCollisions_selected
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredConcreteFinalCall_call
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredLoopCall_call

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


