-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryPreparedState
-- name    : Submission_ThreeSum_LightTernaryPreparedState
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:42:39.45911+00:00
-- url     : https://prove2.me/theorems/cf73e9cd-abb9-40d9-b385-bc7c97b73f1a
-- title:
--   Light Ternary Prepared State
-- statement:
--   Definitions and structural lemmas for Light Ternary Prepared State, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPreparedState.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryPreparedWanted
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightTernaryPreparedState
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryBankStageModel ThreeSum.LightTernaryNearPair ThreeSum.LightTernaryQueryPlan
open ThreeSum.LightTernaryPreparedWanted
set_option maxHeartbeats 6000000
structure Snapshot (lim : Limits) {N : ℕ} (out bankValues caps : ℕ) (f g : Config)
    (μ : ℕ→ℤ) (Q : TritWord N) (E : Enumeration N f.T f.nb) (F G : TritWord N→ℤ) : Prop where
  fResources : Resources lim (rows Q f.T) f F
  gResources : Resources lim (rows Q f.T) g G
  outside : f.T<rank Q
  ga : g.a=f.a
  gp : g.powers=f.powers
  gactive : g.activeBase=f.activeBase
  gbank : g.bank=f.bank
  gnb : g.nb=f.nb
  gT : g.T=f.T
  bankRead : ∀ j<f.nb, μ (f.bank+j)=(address (E.word j) : ℤ)
  bankSorted : ∀ j k, j<k → k<f.nb → address (E.word j)<address (E.word k)
  Fbank : ∀ j<f.nb, μ (f.bv+j)=binomialZeta F (E.word j)
  Gbank : ∀ j<f.nb, μ (g.bv+j)=binomialZeta G (E.word j)
  bankBefore : f.bank+f.nb≤f.a
  Fbefore : f.bv+f.nb≤f.a
  Gbefore : g.bv+f.nb≤f.a
  Hbefore : bankValues+(N+1)*f.nb≤f.a
  Hbank : LightTernaryBankSweep.Stages E
    (fun k => stageValue k (LightTernaryWantedQuery.H F G)) bankValues N μ
  dst : f.a+rows Q f.T≤caps
  caps : caps+N≤f.activeBase
  active : f.activeBase+N≤f.powers
  setupWord : ((4^(N+1) : ℕ) : ℤ)≤lim.word
  GRead : ReadBefore N (rows Q f.T) g f.ws
  FbeforeG : f.vals+rows Q f.T≤g.ws
  Fout : f.vals+rows Q f.T≤out
  Gout : g.vals+rows Q f.T≤out
  outSpace : out+rows Q f.T≤lim.space
  outKeep : f.ws≤out
  productWord : (f.U : ℤ)*(g.U : ℤ)≤lim.word
  queryWord : 4*((4^N : ℕ) : ℤ)*((f.U*g.U : ℕ) : ℤ)+3≤lim.word
structure Plan (lim : Limits) {N : ℕ} (out bankValues caps : ℕ) (f g : Config)
    (Q : TritWord N) (E : Enumeration N f.T f.nb) (F G : TritWord N→ℤ) : Prop where
  fResources : Resources lim (rows Q f.T) f F
  gResources : Resources lim (rows Q f.T) g G
  outside : f.T<rank Q
  ga : g.a=f.a
  gp : g.powers=f.powers
  gactive : g.activeBase=f.activeBase
  gbank : g.bank=f.bank
  gnb : g.nb=f.nb
  gT : g.T=f.T
  bankSorted : ∀ j k, j<k → k<f.nb → address (E.word j)<address (E.word k)
  bankBefore : f.bank+f.nb≤f.a
  Fbefore : f.bv+f.nb≤f.a
  Gbefore : g.bv+f.nb≤f.a
  Hbefore : bankValues+(N+1)*f.nb≤f.a
  dst : f.a+rows Q f.T≤caps
  caps : caps+N≤f.activeBase
  active : f.activeBase+N≤f.powers
  setupWord : ((4^(N+1) : ℕ) : ℤ)≤lim.word
  GRead : ReadBefore N (rows Q f.T) g f.ws
  FbeforeG : f.vals+rows Q f.T≤g.ws
  Fout : f.vals+rows Q f.T≤out
  Gout : g.vals+rows Q f.T≤out
  outSpace : out+rows Q f.T≤lim.space
  outKeep : f.ws≤out
  productWord : (f.U : ℤ)*(g.U : ℤ)≤lim.word
  queryWord : 4*((4^N : ℕ) : ℤ)*((f.U*g.U : ℕ) : ℤ)+3≤lim.word
end ThreeSum.LightTernaryPreparedState


