-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
-- name    : Submission_Weighted_Global_TernaryActualColoredRuntime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:32:07.142457+00:00
-- url     : https://prove2.me/theorems/dc6f79f1-ca07-455a-8d42-0081b3f57922
-- title:
--   Ternary Actual Colored Runtime
-- statement:
--   Definitions and structural lemmas for Ternary Actual Colored Runtime, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualColoredRuntime.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualRuntimeParameters
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramBudget
import Definitions.Def_Submission_Weighted_Global_TernaryActualCleanupRuntime
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalActualColoredRuntime
open Light Real Filter StageBounds ArithmeticStageBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalActualSeedRuntime WeightedGlobalEntropyRates
open WeightedGlobalOversizePrime WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
open scoped Topology BigOperators
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable
def exponent : ℝ :=2400349271/1250000000
def J (m β κ n : ℕ) :=WeightedGlobalSignedPadding.paddedLength β (n^κ) (radixLength m n)
def envelope (C : ℝ) (degree m β κ n : ℕ) : ℕ :=
  ⌈C*(J m β κ n+1:ℕ)^degree*(2:ℝ)^J m β κ n*
    (n:ℝ)^WeightedGlobalCountFrontendBudget.frontendExponent⌉₊
structure NativeBounds {K k m F : ℕ} (maps : Fin F→Weight m (nativePrime K m))
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input)
    (n U κ carries D E j : ℕ) : Prop where
  left : I.nB≤n
  right : I.nC≤n
  requesters : I.requesterCount≤n*carries
  word : WeightedGlobalFrontendResources.eulerBound (N m j)
    (valueCap (r:=j) maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) I)≤D*(n+U+1)^E
  query : I.queryTime≤WeightedGlobalCountFrontendBudget.queryMax m j
    (nativeHost (K:=K) (k:=k) j maps Q I).front.f (nativeHost (K:=K) (k:=k) j maps Q I).front.g
structure State (K m : ℕ) where
  arena : Inputs
  phase : ℕ→Input
  seeds : (j seed : ℕ)→LightWeightedGlobalSeedScoreFactory.Data
    (config (nativePrime K m) j (phase j) arena seed)
  post : Input
  cleanup : LightOriginalSurvivorPair.Layout
  keysB : ℕ→ℕ
  keysC : ℕ→ℕ
structure Fits {K k m F : ℕ} (maps : Fin F→Weight m (nativePrime K m))
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (S : State K m)
    (β κ n D E B : ℕ) : Prop where
  dimension : S.arena.J=J m β κ n
  phases : ∀j≤radixLength m n,NativeBounds (k:=k) maps Q (S.phase j)
    n (n^κ) κ (2^S.arena.J) D E j
  post : NativeBounds (k:=k) maps Q S.post n (n^κ) κ (2^S.arena.J) D E (radixLength m n)
  seedB : ∀j≤radixLength m n,∀s,(S.seeds j s).bB≤B
  seedC : ∀j≤radixLength m n,∀s,(S.seeds j s).bC≤B
  seedO : ∀j≤radixLength m n,∀s,(S.seeds j s).bO≤B
  nA : S.cleanup.nA≤n
  nB : S.cleanup.nB≤n
  nC : S.cleanup.nC≤n
  modulus : S.cleanup.q=(nativePrime K m)^radixLength m n
  width : S.cleanup.L≤2*fixedLength m*S.arena.J
  collisionB : ((TernaryOriginalCollisions.collisionPairs
    (fun i : Fin S.cleanup.nB=>S.keysB i.val)).card:ℝ)≤(n:ℝ)^(7483/10000:ℝ)
  collisionC : ((TernaryOriginalCollisions.collisionPairs
    (fun i : Fin S.cleanup.nC=>S.keysC i.val)).card:ℝ)≤(n:ℝ)^(7483/10000:ℝ)
def hostInputs {K m : ℕ} (S : State K m) (n : ℕ) : ℕ→Input :=
  Function.update S.phase (radixLength m n) S.post
def reporterCoefficient (K k c d m F D E κ B H : ℕ) : ℝ :=
  (WeightedGlobalMomentReporterBudget.reporterConstant H:ℝ)*
    (hostConstant K k c d m F D E κ+4*volumeConstant K k c d m)
def postCoefficient (K k c d m F D E κ B H : ℕ) : ℝ :=
  reporterCoefficient K k c d m F D E κ B H+
    1000000*(fixedLength m+1:ℕ)*(volumeConstant K k c d m+1)
def coefficient (K k c d m F D E κ B H : ℕ) : ℝ :=
  prefixConstant K k c d m F D E κ B+postCoefficient K k c d m F D E κ B H+1
def uniformTime (K k c d m F D E κ B H β n : ℕ) : ℕ :=
  LightWeightedGlobalColorPreparationProof.time n (J m β κ n) (n^κ)+
    LightWeightedGlobalArenaTemplate.time E+LightTernaryInitialBudgets.time K+
      envelope (coefficient K k c d m F D E κ B H)
        (seedPolynomialD K (nativePrime K m) B+6) m β κ n+10000
def time {K k m F : ℕ} (maps : Fin F→Weight m (nativePrime K m))
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (S : State K m) (E κ Hdet n : ℕ) : ℕ :=
  LightWeightedGlobalColorPreparationProof.time n S.arena.J (n^κ)+LightWeightedGlobalArenaTemplate.time E+
    LightTernaryInitialBudgets.time K+allPrefixTime (K:=K) (k:=k) maps Q S.phase S.arena S.seeds n+
      (LightWeightedGlobalPreparedPostSelection.time
        (nativeHost (K:=K) (k:=k) (radixLength m n) maps Q S.post) Hdet S.cleanup S.keysB S.keysC+673)+10000
end ThreeSum.WeightedGlobalActualColoredRuntime


