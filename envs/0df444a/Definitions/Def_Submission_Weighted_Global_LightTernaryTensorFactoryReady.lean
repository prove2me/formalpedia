-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryReady
-- name    : Submission_Weighted_Global_LightTernaryTensorFactoryReady
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:30:38.090888+00:00
-- url     : https://prove2.me/theorems/b3dc6af9-dd17-4310-b738-cfbf4e43b203
-- title:
--   Light Ternary Tensor Factory Ready
-- statement:
--   Definitions and structural lemmas for Light Ternary Tensor Factory Ready, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryTensorFactoryReady.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactory
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedGlobalTensorFactory
open Light TernaryJointType
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
structure Ready {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (lim : Limits) (d K J config ls rs tensor quad powers cols potPowers : ℕ)
    (μ : ℕ→ℤ) (L R : ℕ→ℕ→ℤ) (U : ℕ) (V : ℤ) : Prop where
  immutable : WeightedSourceCountExecutionFactory.Immutable S tensor
  seed : ∀ q<(J+2)^4, WeightedSourceCountExecutionFactory.Seed S lim (d+2)
    S.left.weightBase μ (leftWeights J q L) (rightWeights J q R)
  wordSpace : (lim.space : ℤ)≤lim.word
  depth : d+4<lim.depth
  tensorEnd : tensor+S.front.count*(J+2)^4≤quad
  quadEnd : quad+4≤powers
  powersEnd : powers+5≤S.left.weightBase
  leftEnd : S.left.weightBase+S.left.NL≤S.right.weightBase
  rightSpace : S.right.weightBase+S.right.NL≤lim.space
  countAfter : S.left.weightBase≤S.front.dst
  countSpace : S.front.dst+S.front.count≤lim.space
  configEnd : config+106≤tensor
  leftInputEnd : ls+S.left.NL*(J+2)≤tensor
  rightInputEnd : rs+S.right.NL*(J+2)≤tensor
  configRead : ∀ i<106, μ (config+i)=S.argv.getD i 0
  leftRead : ∀ i<S.left.NL, ∀ j<J+2,
    μ (ls+i*(J+2)+TernarySignedLayout.offset J j)=L i j
  rightRead : ∀ i<S.right.NL, ∀ j<J+2,
    μ (rs+i*(J+2)+TernarySignedLayout.offset J j)=R i j
  leftBound : ∀ i<S.left.NL, ∀ j<J+2, |L i j|≤(U : ℤ)
  rightBound : ∀ i<S.right.NL, ∀ j<J+2, |R i j|≤(U : ℤ)
  channelWord : ((U : ℤ)+1)^2≤lim.word
  indexWord : ((J+3 : ℕ) : ℤ)≤lim.word
  countWord : (S.front.count : ℤ)≤lim.word
  radixWord : (((J+2)^4 : ℕ) : ℤ)≤lim.word
  rowWord : (LightWeightRow.word 4 (J+2) ((J+2)^4) 0 1 : ℤ)≤lim.word
  potentialCols : cols+TernaryPairedColumnEnumeration.width K≤lim.space
  potentialPowers : potPowers+(TernaryPairedColumnEnumeration.width K+1)≤lim.space
  colsAfter : quad≤cols
  potentialPowersAfter : quad≤potPowers
  potentialApart : Apart potPowers (TernaryPairedColumnEnumeration.width K+1)
    cols (TernaryPairedColumnEnumeration.width K)
  scoreNonneg : 0≤V
  scoreBound : ∀ w<S.front.count, ∀ q<(J+2)^4, |score S J L R w q|≤V
  kernelWord : LightTernaryPairedPotential.word K (J+2) V≤lim.word
  polyWord : (LightTernaryPairedPolynomial.polynomial K).coefficient*
    (V+1)^(LightTernaryPairedPolynomial.polynomial K).degree≤lim.word
  sumWord : (S.front.count : ℤ)*((J+2)^TernaryPairedColumnEnumeration.width K : ℕ)*
    (LightTernaryPairedPolynomial.polynomial K).bound V≤lim.word
end ThreeSum.LightWeightedGlobalTensorFactory


