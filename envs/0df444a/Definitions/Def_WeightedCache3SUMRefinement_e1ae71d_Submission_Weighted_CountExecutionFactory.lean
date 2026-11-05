-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountExecutionFactory
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountExecutionFactory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:20:22.586056+00:00
-- url     : https://prove2.me/theorems/0c1f0515-8282-4f5e-98f8-faa9a577e9e1
-- title:
--   CountExecutionFactory
-- statement:
--   Definitions and structural lemmas for CountExecutionFactory, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/CountExecutionFactory.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountHost
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrontendResources
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedCountExecutionFactory
open Light TernaryJointType TernaryBank TernaryCodeSemantics
open WeightedBankStageModel
open WeightedBankEnumeration (cacheCost)
open LightWeightedNearPair LightWeightedWantedRowDispatch LightWeightedPreparedState
open LightSubsetAddress
structure Setup (N : ℕ) where
  f : Config
  g : Config
  Qstar : TritWord N
  Q : ℕ→TritWord N
  group : ℕ→ℕ
  E : Enumeration N f.T f.nb
  bankPowers : ℕ
  keyBase : ℕ
  groups : ℕ
  fsource : ℕ
  gsource : ℕ
  fbase : ℕ
  gbase : ℕ
  hbase : ℕ
  out : ℕ
  caps : ℕ
  records : ℕ
  count : ℕ
  dst : ℕ
  V : ℕ
  t : ℕ
def Setup.argv {N : ℕ} (S : Setup N) : List ℤ :=
  LightWeightedCountFrontend.args S.f S.g S.Qstar S.bankPowers S.keyBase S.groups
    S.fsource S.gsource S.fbase S.gbase S.hbase S.out S.caps S.records S.count S.dst
def Setup.runtime {N : ℕ} (S : Setup N) : ℕ :=
  LightWeightedCountFrontend.time S.groups N S.f.L S.f.nb S.count S.t
structure Ready {N : ℕ} (S : Setup N) (lim : Limits) (d : ℕ) (μ : ℕ→ℤ)
    (F G : ℕ→TritWord N→ℤ) : Prop where
  hw : (lim.space : ℤ)≤lim.word
  ha : S.f.bank+S.f.nb≤S.keyBase
  hfs : S.fsource+S.groups*S.f.nb≤S.keyBase
  hgs : S.gsource+S.groups*S.f.nb≤S.keyBase
  hmeta : S.keyBase+4*S.f.nb≤S.bankPowers
  hpows : S.bankPowers+(2*N+1)≤S.fbase
  hfg : S.fbase+S.groups*((N+1)*S.f.nb)≤S.gbase
  hgh : S.gbase+S.groups*((N+1)*S.f.nb)≤S.hbase
  hHdst : S.hbase+S.groups*((N+1)*S.f.nb)≤S.dst
  hword : ((S.f.nb+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word
  hNword : 2*(N : ℤ)+3≤lim.word
  hgroupsWord : (S.groups : ℤ)+1≤lim.word
  hcodes : ∀ j<S.f.nb, μ (S.f.bank+j)=(address (S.E.word j) : ℤ)
  hsorted : ∀ j k, j<k → k<S.f.nb → address (S.E.word j)<address (S.E.word k)
  hF : ∀ bucket<S.groups, ∀ R, |F bucket R|≤(S.V : ℤ)
  hG : ∀ bucket<S.groups, ∀ R, |G bucket R|≤(S.V : ℤ)
  hforwardWord : 4*((4^N*S.V : ℕ) : ℤ)+3≤lim.word
  hproductWord : (LightWeightedBankAssembly.valueBound N S.V : ℤ)≤lim.word
  hinverseWord : 4*((4^N*LightWeightedBankAssembly.valueBound N S.V : ℕ) : ℤ)+3≤lim.word
  hL : S.f.L≤2*N
  hn : S.f.nb<2^S.f.L
  hrecords : S.records+3*S.count≤S.keyBase
  hdst : S.dst+S.count≤S.f.a
  hspace : S.f.a≤lim.space
  hreadGroup : ∀ j<S.count, μ (S.records+3*j+2)=(S.group j : ℤ)
  hreadQ : ∀ j<S.count, μ (S.records+3*j+1)=(address (S.Q j) : ℤ)
  hgroup : ∀ j<S.count, S.group j<S.groups
  hRank : ∀ j<S.count, cacheCost (S.Q j)=cacheCost S.Qstar
  hcountWord : (S.count : ℤ)+1≤lim.word
  hstrideWord : (((N+1)*S.f.nb : ℕ) : ℤ)≤lim.word
  htailWord : ((N*S.f.nb : ℕ) : ℤ)≤lim.word
  hplan : ∀ j<S.count, Plan lim S.out (S.hbase+S.group j*((N+1)*S.f.nb)) S.caps
      (sourceConfig S.f S.fbase ((N+1)*S.f.nb) (N*S.f.nb) (S.group j))
      (sourceConfig S.g S.gbase ((N+1)*S.f.nb) (N*S.f.nb) (S.group j))
      (S.Q j) S.E (F (S.group j)) (G (S.group j))
  htime : ∀ j<S.count, LightWeightedPreparedWanted.time
      (sourceConfig S.f S.fbase ((N+1)*S.f.nb) (N*S.f.nb) (S.group j))
      (sourceConfig S.g S.gbase ((N+1)*S.f.nb) (N*S.f.nb) (S.group j)) (S.Q j)≤S.t
  hd : d+3*N+S.f.L+16≤lim.depth
end ThreeSum.WeightedCountExecutionFactory
end
end WeightedCache3SUMRefinement_e1ae71d


