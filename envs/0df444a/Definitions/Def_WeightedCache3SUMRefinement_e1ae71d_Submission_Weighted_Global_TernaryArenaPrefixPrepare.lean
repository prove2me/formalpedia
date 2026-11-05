-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixPrepare
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixPrepare
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:14:19.307318+00:00
-- url     : https://prove2.me/theorems/35fec6a2-d69a-4f78-93a5-66177f85c8b0
-- title:
--   TernaryArenaPrefixPrepare
-- statement:
--   Definitions and structural lemmas for TernaryArenaPrefixPrepare, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPrefixPrepare.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedCandidate
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPrefixPrepare
open Light WeightedGlobalLocalParameters TernaryJointType WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup
open LightWeightedGlobalPrefixStep
set_option maxHeartbeats 1000000
set_option maxRecDepth 24000
def inputs (p m F j J n U0 a b scale : ℕ) (I : Input)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) : Inputs where
  m:=m
  F:=F
  p:=p
  seed:=addr I.free I.capacity 3
  template:=addr I.free I.capacity 0
  liveHeader:=addr I.free I.capacity 1
  prefixFree:=addr I.free I.capacity 13
  alpha2:=fixedAlpha m 2
  alphaRank:=alphaRank m
  localQ:=TernaryCodeSemantics.address Q.val
  radix:=4^(fixedLength m)
  J:=J
  a:=a
  b:=b
  scale:=scale
  j:=j
  power:=p^j
  Fbase:=addr I.free I.capacity 50
  Gbase:=addr I.free I.capacity 51
  xB:=p^j
  xC:=p^j
  xP:=a^j
  tB:=9^j*(n*n)
  tC:=9^j*(n*n)
  tP:=U0*(b*scale)^j
def scalars (X : Inputs) : List ℕ :=
  [X.j+1,X.m,X.p,X.power,X.alpha2,X.alphaRank,X.localQ,X.radix,X.J,
   LightWeightedGlobalPrefixSetup.N X.m (X.j+1),LightWeightedGlobalPrefixSetup.T X.m (X.j+1),
   2*LightWeightedGlobalPrefixSetup.N X.m (X.j+1),X.F^(X.j+1),LightWeightedGlobalPrefixSetup.nb X.m (X.j+1),
   X.power*X.p,X.alpha2*(X.j+1),2^(X.alpha2*(X.j+1)),X.alphaRank*(X.j+1),
   (LightWeightedGlobalPrefixSetup.N X.m (X.j+1)+1)*LightWeightedGlobalPrefixSetup.nb X.m (X.j+1),
   LightWeightedGlobalPrefixSetup.N X.m (X.j+1)*LightWeightedGlobalPrefixSetup.nb X.m (X.j+1),
   (2738*(X.alphaRank*(X.j+1))+6*(X.alpha2*(X.j+1))),(2738*(X.alphaRank*(X.j+1))+6*(X.alpha2*(X.j+1)))-LightWeightedGlobalPrefixSetup.T X.m (X.j+1)-1,
   LightTernaryRepeatWord.value X.localQ X.radix (X.j+1),
   X.xB*X.p,X.xC*X.p,X.xP*X.a,X.tB*9,X.tC*9,X.tP*X.b*X.scale,X.tP*X.b,9]
def footprint (X : Inputs) : ℕ :=4^(LightWeightedGlobalPrefixSetup.N X.m (X.j+1))+2*LightWeightedGlobalPrefixSetup.N X.m (X.j+1)+9
def envelope (X : Inputs) : ℕ :=
  106+LightWeightedGlobalPrefixSetup.word X.m (X.j+1) X.F+footprint X+(scalars X).sum
end ThreeSum.WeightedGlobalArenaPrefixPrepare
end
end WeightedCache3SUMRefinement_e1ae71d


