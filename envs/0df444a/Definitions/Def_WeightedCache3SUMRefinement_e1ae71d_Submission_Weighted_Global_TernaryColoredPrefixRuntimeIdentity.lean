-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPrefixRuntimeIdentity
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPrefixRuntimeIdentity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:04:22.584251+00:00
-- url     : https://prove2.me/theorems/b551d118-b3ef-4028-9475-99fb5513f9c8
-- title:
--   TernaryColoredPrefixRuntimeIdentity
-- statement:
--   Definitions and structural lemmas for TernaryColoredPrefixRuntimeIdentity, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredPrefixRuntimeIdentity.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualColoredRuntime
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


