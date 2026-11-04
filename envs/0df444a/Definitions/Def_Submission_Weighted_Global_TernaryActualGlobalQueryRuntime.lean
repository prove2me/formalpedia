-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
-- name    : Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:47:29.509107+00:00
-- url     : https://prove2.me/theorems/6835c255-9f43-43c8-9d48-92aa3f4862c4
-- title:
--   Ternary Actual Global Query Runtime
-- statement:
--   Definitions and structural lemmas for Ternary Actual Global Query Runtime, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualGlobalQueryRuntime.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalActualGlobalQueryRuntime
open Light Real Filter StageBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalActualSeedRuntime WeightedGlobalActualColoredRuntime
open WeightedGlobalOversizePrime WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale WeightedGlobalEntropyRates
open scoped Topology BigOperators
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable
def zeroInput (I : Input) : Input :={I with queryTime:=0}
def zeroState {K m : ℕ} (S : State K m) : State K m where
  arena:=S.arena
  phase:=fun j=>zeroInput (S.phase j)
  seeds:=S.seeds
  post:=zeroInput S.post
  cleanup:=S.cleanup
  keysB:=S.keysB
  keysC:=S.keysC
def queryCap {K m : ℕ} (S : State K m) (n : ℕ) : ℕ :=
  max ((Finset.range (radixLength m n+1)).sup (fun j=>(S.phase j).queryTime)) S.post.queryTime
def wantedCap (K k m F n digitLength : ℕ) : ℕ :=
  n*2^digitLength*(outputCap K k m F)^radixLength m n
def extraCoefficient (K k c d m F D E κ B H : ℕ) : ℝ :=
  ((16*menuCoefficient K (nativePrime K m)+(TernaryMomentSchedule.channels (2*H+1)).length:ℕ):ℝ)*
    (WeightedGlobalUniformQueryTime.coefficient m D E κ:ℝ)*volumeConstant K k c d m
def uniformTime (K k c d m F D E κ B H β n : ℕ) : ℕ :=
  WeightedGlobalActualColoredRuntime.uniformTime K k c d m F D E κ B H β n+
    WeightedGlobalActualColoredRuntime.envelope (extraCoefficient K k c d m F D E κ B H) 10 m β κ n
def prefixCorrection {K m : ℕ} (k F : ℕ) (S : State K m) (n : ℕ) : ℕ :=
  radixLength m n*(menuSize K m S.arena.J*menuSize K m S.arena.J+1)*(S.arena.J+2)^4*
    wantedCap K k m F n S.arena.J*queryCap S n
def totalCorrection {K m : ℕ} (k F Hdet : ℕ) (S : State K m) (n : ℕ) : ℕ :=
  prefixCorrection k F S n+(TernaryMomentSchedule.channels (2*Hdet+1)).length*
    wantedCap K k m F n S.arena.J*queryCap S n
end ThreeSum.WeightedGlobalActualGlobalQueryRuntime


