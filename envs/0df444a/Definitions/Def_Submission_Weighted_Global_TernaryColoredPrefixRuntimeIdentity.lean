-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixRuntimeIdentity
-- name    : Submission_Weighted_Global_TernaryColoredPrefixRuntimeIdentity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:06:37.651939+00:00
-- url     : https://prove2.me/theorems/59531303-7dc5-44c4-ae5d-9ae73fb66ec3
-- title:
--   Ternary Colored Prefix Runtime Identity
-- statement:
--   Definitions and structural lemmas for Ternary Colored Prefix Runtime Identity, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPrefixRuntimeIdentity.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredPrefixRuntimeIdentity
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaLoop
open LightWeightedGlobalSeedScoreFactory WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup
open WeightedGlobalActualSeedRuntime
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
def prefixData {p m F K N : ℕ} [Fact p.Prime]
    {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
    (S : Setup p m F K N E) : (j seed : ℕ)→Data (config p j S.input S.arrays seed)
  | 0, _ => {
      oldB:=fun _=>0
      oldC:=fun _=>0
      oldO:=fun _=>0
      B:=fun _ _=>0
      Cvalues:=fun _ _=>0
      O:=fun _ _=>0
      coeff:=fun _=>0
      position:=S.input.positions
      catalog:=fun _ _=>0
      logicalRows:=[]
      logicalRow:=0
      bB:=S.featureBound
      bC:=S.featureBound
      bO:=S.featureBound }
  | j+1, seed => WeightedGlobalArenaPhase.dataAt S.input S.arrays j S.featureBound S.ell
      (WeightedGlobalArenaFamilyBudget.seedAt S.enumeration) S.L S.R S.O (S.state j) (fun _ _=>0) seed
variable {κ : ℕ}
def runtimeState (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (μ : ℕ→ℤ)
    [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
    (post : Input) (cleanup : LightOriginalSurvivorPair.Layout) (keysB keysC : ℕ→ℕ) :
    WeightedGlobalActualColoredRuntime.State P.K P.m where
  arena:=(setup P n free menu c A B C μ).arrays
  phase:=fun _=>(setup P n free menu c A B C μ).input
  seeds:=prefixData (setup P n free menu c A B C μ)
  post:=post
  cleanup:=cleanup
  keysB:=keysB
  keysC:=keysC
end ThreeSum.WeightedGlobalColoredPrefixRuntimeIdentity


