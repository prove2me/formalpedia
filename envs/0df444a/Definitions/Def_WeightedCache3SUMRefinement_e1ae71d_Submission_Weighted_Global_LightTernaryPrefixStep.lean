-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixStep
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:57:10.951763+00:00
-- url     : https://prove2.me/theorems/f7c4ca57-4706-410b-8a4d-517e643b92dd
-- title:
--   LightTernaryPrefixStep
-- statement:
--   Definitions and structural lemmas for LightTernaryPrefixStep, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPrefixStep.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixPrepare
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixFinish
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedGlobalPrefixStep
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
structure Inputs where
  m : ℕ
  F : ℕ
  p : ℕ
  seed : ℕ
  template : ℕ
  liveHeader : ℕ
  prefixFree : ℕ
  alpha2 : ℕ
  alphaRank : ℕ
  localQ : ℕ
  radix : ℕ
  J : ℕ
  a : ℕ
  b : ℕ
  scale : ℕ
  j : ℕ
  power : ℕ
  Fbase : ℕ
  Gbase : ℕ
  xB : ℕ
  xC : ℕ
  xP : ℕ
  tB : ℕ
  tC : ℕ
  tP : ℕ
def Inputs.argv (X : Inputs) : List ℤ :=
  stepArgs X.m X.F X.p X.seed X.template X.liveHeader X.prefixFree X.alpha2 X.alphaRank X.localQ X.radix X.J
    X.a X.b X.scale X.j X.power
def Prepared (X : Inputs) (μ ν : ℕ→ℤ) : Prop :=
  ∃μ₁ μ₂,
    Seg μ₁ (LightWeightedGlobalPrefixSetup.headerAt X.prefixFree X.m (X.j+1))
      (LightWeightedGlobalPrefixSetup.header X.m (X.j+1) X.F X.prefixFree (LightWeightedGlobalPrefixSetup.workAt X.prefixFree X.m (X.j+1))) ∧
    Seg μ₁ X.prefixFree ((WeightedAddresses.codes (LightWeightedGlobalPrefixSetup.N X.m (X.j+1))
      (LightWeightedGlobalPrefixSetup.T X.m (X.j+1))).map (fun (c:ℕ)=>(c:ℤ))) ∧
    LightSubsetAddress.Powers μ₁ (LightWeightedGlobalPrefixSetup.workAt X.prefixFree X.m (X.j+1))
      (2*LightWeightedGlobalPrefixSetup.N X.m (X.j+1)) ∧ Kept μ μ₁ X.prefixFree ∧
    LightWeightedGlobalPrefixPrepare.HeaderReceipt μ₁ μ₂ X.m X.F X.p X.template X.liveHeader X.prefixFree X.alpha2 X.alphaRank
      X.localQ X.radix X.J X.j X.power X.Fbase X.Gbase ∧
    SameOutside μ₁ μ₂ X.liveHeader 106 ∧
    ν=LightTernaryBudgetStep.changed (LightWeightedGlobalPrefixPrepare.seedChanged μ₂ X.seed X.power X.liveHeader (X.j+1))
      (X.seed+41) X.p X.a X.b X.scale X.xB X.xC X.xP X.tB X.tC X.tP
structure PrepareReady (X : Inputs) (lim : Limits) (depth : ℕ) (μ : ℕ→ℤ) : Prop where
  spaceWord : (lim.space:ℤ)≤lim.word
  prefixSpace : LightWeightedGlobalPrefixSetup.endAt X.prefixFree X.m (X.j+1)≤lim.space
  prefixWord : (LightWeightedGlobalPrefixSetup.word X.m (X.j+1) X.F:ℤ)≤lim.word
  depthBound : depth+LightWeightedGlobalPrefixSetup.N X.m (X.j+1)+5≤lim.depth
  jWord : ((X.j+1:ℕ):ℤ)≤lim.word
  templateEnd : X.template+106≤X.liveHeader
  headerEnd : X.liveHeader+106≤X.seed
  seedEnd : X.seed+48≤X.prefixFree
  Fread : μ (X.template+99)=(X.Fbase:ℤ)
  Gread : μ (X.template+100)=(X.Gbase:ℤ)
  cutoff : LightWeightedGlobalPrefixSetup.T X.m (X.j+1)+2739≤(2738*(X.alphaRank*(X.j+1))+6*(X.alpha2*(X.j+1)))
  Nword : (LightWeightedGlobalPrefixSetup.N X.m (X.j+1):ℤ)+1≤lim.word
  scalarWords : ∀x∈(LightWeightedGlobalPrefixHeader.args X.template X.liveHeader
      (LightWeightedGlobalPrefixSetup.headerAt X.prefixFree X.m (X.j+1)) (X.j+1) X.m X.p X.power X.alpha2 X.alphaRank X.localQ X.radix X.J++
      LightWeightedGlobalPrefixHeader.locals (LightWeightedGlobalPrefixSetup.N X.m (X.j+1))
        (LightWeightedGlobalPrefixSetup.T X.m (X.j+1)) (2*LightWeightedGlobalPrefixSetup.N X.m (X.j+1))
        (X.F^(X.j+1)) (LightWeightedGlobalPrefixSetup.nb X.m (X.j+1)) X.prefixFree
        (LightWeightedGlobalPrefixSetup.workAt X.prefixFree X.m (X.j+1)) (X.j+1) X.p X.power X.alpha2 X.alphaRank X.localQ X.radix X.Fbase X.Gbase),
      |x|≤lim.word
  factorWords : ∀i≤X.alpha2*(X.j+1), ((2^i:ℕ):ℤ)≤lim.word
  queryWords : ∀i≤X.j+1, (LightTernaryRepeatWord.value X.localQ X.radix i:ℤ)≤lim.word
  budgetRead : Seg μ (X.seed+41) (LightTernaryBudgetStep.oldValues X.xB X.xC X.xP X.tB X.tC X.tP)
  budgetWords : ∀x∈LightTernaryBudgetStep.nextValues X.p X.a X.b X.scale X.xB X.xC X.xP X.tB X.tC X.tP,x≤lim.word
  midWord : ((X.tP*X.b:ℕ):ℤ)≤lim.word
  nineWord : (9:ℤ)≤lim.word
def time (X : Inputs) (C : Config) (n seedTime : ℕ) : ℕ :=
  LightWeightedGlobalPrefixPrepare.time X.m X.j X.alpha2+LightWeightedGlobalPrefixFinish.time C n seedTime (X.power*X.p)+500
end ThreeSum.LightWeightedGlobalPrefixStep
end
end WeightedCache3SUMRefinement_e1ae71d


