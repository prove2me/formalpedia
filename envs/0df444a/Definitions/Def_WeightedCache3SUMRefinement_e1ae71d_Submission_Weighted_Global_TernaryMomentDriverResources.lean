-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentDriverResources
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentDriverResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:21:53.28405+00:00
-- url     : https://prove2.me/theorems/50d1c8b8-d4ec-40b8-b6c0-de8fc793250c
-- title:
--   TernaryMomentDriverResources
-- statement:
--   Definitions and structural lemmas for TernaryMomentDriverResources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryMomentDriverResources.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryCertifiedMomentDriver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairMoments
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


