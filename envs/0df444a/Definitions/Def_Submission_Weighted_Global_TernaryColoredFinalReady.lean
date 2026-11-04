-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalReady
-- name    : Submission_Weighted_Global_TernaryColoredFinalReady
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:15:47.631347+00:00
-- url     : https://prove2.me/theorems/bcd3f799-2428-406c-b3b6-62fb72e5bf1b
-- title:
--   Ternary Colored Final Ready
-- statement:
--   Definitions and structural lemmas for Ternary Colored Final Ready, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredFinalReady.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredTerminalReceipt
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalGuardAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCleanupAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTimeMonotone
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPostABI
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_layout
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalBounds_cells
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalGuardAllocation_guards
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixCommit_layout
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_selected
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedPrimitiveGuards_guards
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedCollisions_selected
import Theorems.Thm_ThreeSum_WeightedGlobalPreparedOriginals_metadata
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredFinalReady
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPostSelection
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalColoredTerminalReceipt
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ → ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
def selected : Input :=
  selectedInput (input P n free A B C) (n ^ κ) P.radix A.length (hash P n free menu c A B C initial)
    (fun i => A.getD i 0) (fun i => B.getD i 0) (fun i => C.getD i 0) (keysB P n free menu c A B C initial)
    (keysC P n free menu c A B C initial)
def cleanup :=
  WeightedGlobalArenaCleanupLayout.layout (input P n free A B C).free (cells P n) (LightTernaryColorPrelude.av free n)
    A.length (LightTernaryColorPrelude.bv free n) B.length (LightTernaryColorPrelude.cv free n) C.length
    (P.p ^ (rounds P n)) (2 * N P.m (rounds P n))
structure Ready (lim : Limits) (d : ℕ) (ν : ℕ → ℤ) : Prop where
  guards :
    WeightedGlobalArenaPostCertificate.Guards (r := rounds P n) P.maps P.threshold P.cap P.output
      (selected P n free menu c A B C initial) lim (d + 2) P.M n (n ^ κ) P.H B.length C.length
  cleanup :
    LightWeightedGlobalPreparedPostSelection.Inputs (cleanup P n free A B C) lim (d + 3) (n ^ κ)
      (2 * N P.m (rounds P n)) ν (fun i => A.getD i 0) (fun i => B.getD i 0) (fun i => C.getD i 0)
      (keysB P n free menu c A B C initial) (keysC P n free menu c A B C initial)
  metadata :
    WeightedGlobalArenaPostMemory.Metadata (r := rounds P n) P.maps P.threshold (selected P n free menu c A B C initial)
      ν
  host :
    ∀ i < 106,
      i ≠ 11 →
        i ≠ 34 →
          ν (addr (input P n free A B C).free (cells P n) 1 + i) =
            (LightWeightedGlobalCompactReporter.zeroCounts
                  (WeightedGlobalArenaSourceSetup.setup (r := rounds P n) P.maps P.threshold P.cap P.output
                    (selected P n free menu c A B C initial))).argv.getD
              i 0
end ThreeSum.WeightedGlobalColoredFinalReady


