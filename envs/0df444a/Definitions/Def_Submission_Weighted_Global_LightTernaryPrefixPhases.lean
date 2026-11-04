-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixPhases
-- name    : Submission_Weighted_Global_LightTernaryPrefixPhases
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:54:10.527033+00:00
-- url     : https://prove2.me/theorems/3d48c797-ec74-4f28-b372-8370fa151bf5
-- title:
--   Light Ternary Prefix Phases
-- statement:
--   Definitions and structural lemmas for Light Ternary Prefix Phases, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixPhases.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_layout

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedGlobalPrefixPhases
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixLoop
open LightWeightedGlobalPrefixStep
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
structure Phase (X : Inputs) (lim : Limits) (depth K R S p : ℕ)
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ) (μ : ℕ→ℤ) where
  C : Config
  [prime : Fact C.p.Prime]
  family : Family C
  n : ℕ
  U : ℕ
  dB : ℕ
  dC : ℕ
  dP : ℕ
  tB : ℕ
  tC : ℕ
  tP : ℕ
  newSpan : ℕ
  seedTime : ℕ
  programPrime : C.p=p
  leftX : family.xl=xl
  leftY : family.yl=yl
  leftZ : family.zl=zl
  rightX : family.xr=xr
  rightY : family.yr=yr
  rightZ : family.zr=zr
  prepare : PrepareReady X lim (depth+1) μ
  inputPrime : X.p=C.p
  inputJ : X.J=C.J
  plans : ∀ν, Prepared X μ ν→FullPlan C family lim (depth+1) K R S n U dB dC dP tB tC tP newSpan seedTime raws words maps ν
  layout : LightWeightedGlobalPrefixFinish.Layout C lim X.seed (X.power*X.p) newSpan
  headerRead : ∀ν, Prepared X μ ν→Seg ν X.seed (LightWeightedGlobalPrefixFinish.header C n dB dC dP tB tC tP newSpan)
  finalHeader : ∀ν, ∀h : Prepared X μ ν, ∀ξ, (plans ν h).finalState ξ→
    Seg ξ X.seed (LightWeightedGlobalPrefixFinish.header C n dB dC dP tB tC tP newSpan)
attribute [instance] Phase.prime
def Phase.Output {X : Inputs} {lim : Limits} {depth K R S p : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {xl yl zl xr yr zr : List ℤ} {μ : ℕ→ℤ}
    (H : Phase X lim depth K R S p raws words maps xl yl zl xr yr zr μ) (ω : ℕ→ℤ) : Prop :=
  ∃ν, ∃h : Prepared X μ ν, ∃ξ, (H.plans ν h).finalState ξ ∧
    LightWeightedGlobalPrefixFinish.Committed H.C (X.power*X.p) H.newSpan ξ ω ∧
    Seg ω X.seed (LightWeightedGlobalPrefixFinish.header H.C H.n H.dB H.dC H.dP H.tB H.tC H.tP H.newSpan)
def Phase.time {X : Inputs} {lim : Limits} {depth K R S p : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {xl yl zl xr yr zr : List ℤ} {μ : ℕ→ℤ}
    (H : Phase X lim depth K R S p raws words maps xl yl zl xr yr zr μ) : ℕ :=
  LightWeightedGlobalPrefixStep.time X H.C H.n H.seedTime
structure LoopPlan (lim : Limits) (rounds m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale
    depth K R S T : ℕ) (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ) (μ : ℕ→ℤ) where
  invariant : ℕ→(ℕ→ℤ)→Prop
  initial : invariant 0 μ
  roundsWord : (rounds:ℤ)≤lim.word
  depthBound : depth<lim.depth
  powerWords : ∀j≤rounds, ((p^j:ℕ):ℤ)≤lim.word
  inputs : ℕ→Inputs
  arguments : ∀j<rounds, (inputs j).argv=stepArgs m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale j (p^j)
  powers : ∀j<rounds, (inputs j).power*(inputs j).p=p^(j+1)
  stages : ∀j<rounds, ∀ν,invariant j ν→Phase (inputs j) lim (depth+1) K R S p raws words maps xl yl zl xr yr zr ν
  costs : ∀(j : ℕ)(hj : j<rounds),∀ν,∀h:invariant j ν,(stages j hj ν h).time≤T
  transition : ∀(j : ℕ)(hj : j<rounds),∀ν,∀h:invariant j ν,∀ω,(stages j hj ν h).Output ω→invariant (j+1) ω
end ThreeSum.LightWeightedGlobalPrefixPhases


