-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredTerminalReceipt
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredTerminalReceipt
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:07:49.007096+00:00
-- url     : https://prove2.me/theorems/f1c86300-ca73-4321-83a1-8cc31e630e3c
-- title:
--   TernaryColoredTerminalReceipt
-- statement:
--   Definitions and structural lemmas for TernaryColoredTerminalReceipt, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredTerminalReceipt.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaTerminalReceipt
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceControlBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedCollisions
import Theorems.Thm_ThreeSum_TernaryMomentMatrixInvariant_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_initial
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalColoredTerminalReceipt
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalArenaSelectedSigned
open WeightedGlobalColoredLoopSetup LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ → ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
def hash :=
  selectedHash (arrays P n free menu A B C) ((setup P n free menu c A B C initial).state (rounds P n)) (rounds P n)
def keysB (i : ℕ) :=
  TernaryExtensionEncoding.coefficientCode
    (WeightedGlobalNativeRequesterCoverage.sourceLeft (hash P n free menu c A B C initial) (n ^ κ) P.radix (B.getD i 0))
def keysC (i : ℕ) :=
  TernaryExtensionEncoding.coefficientCode
    (WeightedGlobalNativeRequesterCoverage.sourceRight (hash P n free menu c A B C initial) (n ^ κ) P.radix
      (C.getD i 0))
def nativeInput :=
  WeightedGlobalArenaNativeComplete.input (input P n free A B C) (n ^ κ) P.radix A.length
    (hash P n free menu c A B C initial) (fun i => A.getD i 0) (fun i => B.getD i 0) (fun i => C.getD i 0)
structure Receipt (ω : ℕ → ℤ) : Prop where
  immutable : Kept initial ω (input P n free A B C).free
  leftKeys : Reads ω (addr (input P n free A B C).free (cells P n) 4) B.length (keysB P n free menu c A B C initial)
  rightKeys : Reads ω (addr (input P n free A B C).free (cells P n) 5) C.length (keysC P n free menu c A B C initial)
  queries :
    WeightedGlobalArenaTerminalReceipt.QueryReceipt P.maps P.threshold P.cap (rounds P n) P.output
      (nativeInput P n free menu c A B C initial) ω
  zero :
    WeightedGlobalNativeTensorScore.pairedPotential
        (WeightedGlobalArenaSourceSetup.setup (r := rounds P n) P.maps P.threshold P.cap P.output
          (nativeInput P n free menu c A B C initial))
        P.K (J P n) (WeightedGlobalArenaSelectedSigned.left (n ^ κ) P.radix (J P n) (fun i => B.getD i 0))
        (WeightedGlobalArenaSelectedSigned.right (n ^ κ) P.radix (J P n) (fun i => C.getD i 0)) =
      0
end ThreeSum.WeightedGlobalColoredTerminalReceipt
end
end WeightedCache3SUMRefinement_e1ae71d


