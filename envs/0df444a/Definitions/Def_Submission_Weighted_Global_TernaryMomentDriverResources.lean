-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryMomentDriverResources
-- name    : Submission_Weighted_Global_TernaryMomentDriverResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:59:29.032635+00:00
-- url     : https://prove2.me/theorems/f8560b4e-c939-4ed4-980c-6f37a07876a3
-- title:
--   Ternary Moment Driver Resources
-- statement:
--   Definitions and structural lemmas for Ternary Moment Driver Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDriverResources.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryCertifiedMomentDriver
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedGlobalCertifiedMomentDriver
open Light TernaryMomentSchedule LightWeightedGlobalMomentChannelFactory
structure Resources {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (lim : Limits) (d originalB originalC matrix terms a b U W : ℕ)
    (μ : ℕ→ℤ) (B C : ℕ→ℤ) : Prop where
  hseed : ∀ k<terms, ∀ j≤k,
      WeightedSourceCountExecutionFactory.Seed S lim (d+2) S.left.weightBase μ
        (leftWeights k j B) (rightWeights k j C)
  himmutable : WeightedSourceCountExecutionFactory.Immutable S matrix
  hw : (lim.space : ℤ)≤lim.word
  hd : d+2<lim.depth
  hBspace : originalB+S.left.NL≤matrix
  hCspace : originalC+S.right.NL≤matrix
  hwindow : matrix+terms*S.front.count≤S.left.weightBase
  hleft : S.left.weightBase+S.left.NL≤S.right.weightBase
  hright : S.right.weightBase+S.right.NL≤lim.space
  houtBefore : S.left.weightBase≤S.front.dst
  hout : S.front.dst+S.front.count≤lim.space
  hleftSpace : S.left.weightBase≤lim.space
  hB : ∀ i<S.left.NL, μ (originalB+i)=B i
  hC : ∀ i<S.right.NL, μ (originalC+i)=C i
  hBabs : ∀ i<S.left.NL, |B i|≤(U : ℤ)
  hCabs : ∀ i<S.right.NL, |C i|≤(U : ℤ)
  hscore : ∀ k<terms, ∀ j≤k, ∀ i<S.front.count, |score S B C k j i|≤(W : ℤ)
  hleftWord : ∀ k<terms, ∀ j≤k,
      max (U : ℤ) (2*((k.choose j : ℤ)+1)*((U : ℤ)+2)^j)≤lim.word
  hrightWord : ∀ k<terms, ∀ j≤k, max (U : ℤ) (2*((U : ℤ)+1)^(k-j))≤lim.word
  haddWord : 2*(((channels terms).length*W : ℕ) : ℤ)≤lim.word
  htermsWord : (terms : ℤ)≤lim.word
  hargsWord : ∀ z∈LightWeightedGlobalMomentChannelFactory.args S originalB originalC matrix, |z|≤lim.word
  hleftHom : ∀ pair∈S.left.records, WeightedGlobalBank.rank (S.front.E.word (S.left.key pair.2))=a
  hrightHom : ∀ pair∈S.right.records, WeightedGlobalBank.rank (S.front.E.word (S.right.key pair.2))=b
  hQ : ∀ i<S.front.count, WeightedGlobalBank.rank (S.front.Q i)=a+b
end ThreeSum.LightWeightedGlobalCertifiedMomentDriver


