-- Prove2me | Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorResources
-- name    : Submission_ThreeSum_LightOriginalSurvivorResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T10:51:48.255591+00:00
-- url     : https://prove2.me/theorems/6e2c7ec6-0e8e-40b3-8efb-001f0b4b46a0
-- title:
--   Light Original Survivor Resources
-- statement:
--   Definitions and structural lemmas for Light Original Survivor Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivorResources.lean

import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorPair
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightOriginalSurvivorPair
open Light ThreeSum.LightSubsetAddress LightOriginalCollisionCleanup
structure Layout where
  aBase : ℕ
  nA : ℕ
  bBase : ℕ
  nB : ℕ
  cBase : ℕ
  nC : ℕ
  keyB : ℕ
  keyC : ℕ
  histB : ℕ
  histC : ℕ
  q : ℕ
  powers : ℕ
  L : ℕ
  outB : ℕ
  valueB : ℕ
  packedB : ℕ
  lengthB : ℕ
  outC : ℕ
  valueC : ℕ
  packedC : ℕ
  lengthC : ℕ
def Layout.args (c : Layout) : List ℤ :=
  [c.aBase,c.nA,c.bBase,c.nB,c.cBase,c.nC,c.keyB,c.keyC,c.histB,c.histC,c.q,c.powers,c.L,
    c.outB,c.valueB,c.packedB,c.lengthB,c.outC,c.valueC,c.packedC,c.lengthC]
def Layout.Unchanged (c : Layout) (keysB keysC : ℕ → ℕ) (μ ν : ℕ → ℤ) : Prop :=
  ∀ x, LightOriginalSurvivorStage.Unwritten c.outB c.nB c.valueB c.packedB
      (LightOriginalSurvivors.indices keysB c.nB).length c.lengthB x →
    LightOriginalSurvivorStage.Unwritten c.outC c.nC c.valueC c.packedC
      (LightOriginalSurvivors.indices keysC c.nC).length c.lengthC x → ν x = μ x
structure Resources (c : Layout) (lim : Limits) (d U W : ℕ) (μ : ℕ → ℤ)
    (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ) : Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  hA : c.aBase+c.nA ≤ c.outB
  hB : c.bBase+c.nB ≤ c.outB
  hC : c.cBase+c.nC ≤ c.outB
  hkB : c.keyB+c.nB ≤ c.outB
  hkC : c.keyC+c.nC ≤ c.outB
  hhB : c.histB+c.q ≤ c.outB
  hhC : c.histC+c.q ≤ c.outB
  hp : c.powers+(W+1) ≤ c.outB
  hB1 : c.outB+2*c.nB ≤ c.valueB
  hB2 : c.valueB+c.nB ≤ c.packedB
  hB3 : c.packedB+c.nB ≤ c.lengthB
  hBC : c.lengthB+1 ≤ c.outC
  hC1 : c.outC+2*c.nC ≤ c.valueC
  hC2 : c.valueC+c.nC ≤ c.packedC
  hC3 : c.packedC+c.nC ≤ c.lengthC
  hEnd : c.lengthC+1 ≤ lim.space
  hword : ((c.nB+c.nC+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word
  hkeysB : ∀ i < c.nB, keysB i < c.q
  hkeysC : ∀ i < c.nC, keysC i < c.q
  hreadKB : ∀ i < c.nB, μ (c.keyB+i) = (keysB i : ℤ)
  hreadKC : ∀ i < c.nC, μ (c.keyC+i) = (keysC i : ℤ)
  hcountsB : ∀ k < c.q, μ (c.histB+k) = (counts keysB c.nB k : ℤ)
  hcountsC : ∀ k < c.q, μ (c.histC+k) = (counts keysC c.nC k : ℤ)
  hboundA : ∀ i < c.nA, |A i| ≤ U
  hboundB : ∀ i < c.nB, |B i| ≤ U
  hboundC : ∀ i < c.nC, |C i| ≤ U
  hreadA : ∀ i < c.nA, μ (c.aBase+i) = A i
  hreadB : ∀ i < c.nB, μ (c.bBase+i) = B i
  hreadC : ∀ i < c.nC, μ (c.cBase+i) = C i
  hvalueWord : 2*(U : ℤ)+3 ≤ lim.word
  hpowers : Powers μ c.powers W
  hsortedB : ∀ i j, i < j → j < c.nB → B i < B j
  hsortedC : ∀ i j, i < j → j < c.nC → C i < C j
  hL : c.L ≤ W
  hnB : c.nB < 2^c.L
  hnC : c.nC < 2^c.L
  hd : d+c.L+5 ≤ lim.depth
end ThreeSum.LightOriginalSurvivorPair


