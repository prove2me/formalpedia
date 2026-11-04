-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryControllerPlan
-- name    : Submission_Weighted_Global_LightTernaryControllerPlan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:35:59.680212+00:00
-- url     : https://prove2.me/theorems/e4bb7a6d-d840-4403-82f7-c269a5118e6d
-- title:
--   Light Ternary Controller Plan
-- statement:
--   Definitions and structural lemmas for Light Ternary Controller Plan, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryControllerPlan.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerFactory
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_Candidate_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_SpanGuard_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedGlobalControllerFactory
open Light LightWeightedGlobalSeedScoreFactory
structure Plan (C : Config) [Fact C.p.Prime] (D : Family C) (lim : Limits)
    (depth K R S n U dB dC dP tB tC tP newSpan seedTime : ℕ)
    (raws : List ℤ) (words maps : List ℕ) (μ : ℕ→ℤ) where
  invariant : ℕ→(ℕ→ℤ)→Prop
  replay : (ℕ→ℤ)→Prop
  finalState : (ℕ→ℤ)→Prop
  spaceWord : (lim.space:ℤ)≤lim.word
  flags : C.flags+n≤lim.space
  Bscores : C.scoreB+n≤lim.space
  Cscores : C.scoreC+n≤lim.space
  Pscores : C.scorePaired+n≤lim.space
  selectorWord : (LightTernaryRowSelector.word n U dB dC dP tB tC tP:ℤ)≤lim.word
  length : C.J+2≤lim.space
  row : C.menu+(D.pick K n dB dC dP tB tC tP-1)*(C.J+2)≤lim.space
  depthBound : depth<lim.depth
  initial : invariant 0 μ
  candidate : ∀i<n, ∀ν, invariant i ν→(D.candidate i).Guard lim (depth+1) K R S raws words maps ν
  runtime : ∀i<n, (D.candidate i).runtime K R S raws words maps≤seedTime
  nextState : ∀i<n, ∀ν ξ, invariant i ν→(D.candidate i).Done K ν ξ→invariant (i+1) ξ
  reads : ∀ν, invariant n ν→
    (∀i<n, ν (C.flags+i)=D.flag i ∧ |D.flag i|≤1) ∧
    (∀i<n, ν (C.scoreB+i)=D.scoreB i ∧ |D.scoreB i|≤U) ∧
    (∀i<n, ν (C.scoreC+i)=D.scoreC i ∧ |D.scoreC i|≤U) ∧
    (∀i<n, ν (C.scorePaired+i)=D.scoreP K i ∧ |D.scoreP K i|≤U)
  existsRow : ∃i<n, LightTernaryRowSelector.Good D.flag D.scoreB D.scoreC (D.scoreP K)
    dB dC dP tB tC tP i
  replayGuard : ∀ν, invariant n ν→
    (D.candidate (D.pick K n dB dC dP tB tC tP-1)).Guard lim (depth+1) K R S raws words maps ν
  replayState : ∀ν ξ, invariant n ν→(D.candidate (D.pick K n dB dC dP tB tC tP-1)).Done K ν ξ→ replay ξ
  spanGuard : ∀ν, replay ν→SpanGuard (withSeed C (D.pick K n dB dC dP tB tC tP-1))
    (D.candidate (D.pick K n dB dC dP tB tC tP-1)).data lim (depth+1) newSpan ν
  finish : ∀ν ξ, replay ν→SpanDone (withSeed C (D.pick K n dB dC dP tB tC tP-1))
    (D.candidate (D.pick K n dB dC dP tB tC tP-1)).data newSpan ν ξ→ finalState ξ
def Plan.run {C : Config} [Fact C.p.Prime] {D : Family C} {lim : Limits}
    {depth K R S n U dB dC dP tB tC tP newSpan seedTime : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {μ : ℕ→ℤ}
    (H : Plan C D lim depth K R S n U dB dC dP tB tC tP newSpan seedTime raws words maps μ) :=
  ThreeSum.LightWeightedGlobalControllerFactory.run D raws words maps μ H.invariant H.replay H.finalState H.spaceWord H.flags H.Bscores H.Cscores H.Pscores
    H.selectorWord H.length H.row H.depthBound H.initial H.candidate H.runtime H.nextState H.reads H.existsRow
    H.replayGuard H.replayState H.spanGuard H.finish
end ThreeSum.LightWeightedGlobalControllerFactory


