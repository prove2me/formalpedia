-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredTerminalReceipt
-- name    : Submission_Weighted_Global_TernaryColoredTerminalReceipt
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:06:49.855746+00:00
-- url     : https://prove2.me/theorems/8aecf104-c764-4dab-b0bb-1ac73be5f3a6
-- title:
--   Ternary Colored Terminal Receipt
-- statement:
--   Definitions and structural lemmas for Ternary Colored Terminal Receipt, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredTerminalReceipt.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTerminalReceipt
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControlBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedCollisions
import Theorems.Thm_ThreeSum_TernaryMomentMatrixInvariant_zero
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
set_option autoImplicit false
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


