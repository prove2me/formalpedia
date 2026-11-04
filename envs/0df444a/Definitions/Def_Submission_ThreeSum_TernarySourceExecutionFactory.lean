-- Prove2me | Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
-- name    : Submission_ThreeSum_TernarySourceExecutionFactory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:17:31.735628+00:00
-- url     : https://prove2.me/theorems/3b507eb7-183a-4bb8-8c8b-bb3ac5ac482c
-- title:
--   Ternary Source Execution Factory
-- statement:
--   Definitions and structural lemmas for Ternary Source Execution Factory, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceExecutionFactory.lean

import Definitions.Def_Submission_ThreeSum_LightTernarySourceCountHost
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernarySourceExecutionFactory
open Light LightSubsetAddress LightTernarySourceHost
structure Setup where
  xs : List ℤ
  ys : List ℤ
  zs : List ℤ
  base0 : ℕ
  dst0 : ℕ
  base1 : ℕ
  dst1 : ℕ
  base2 : ℕ
  dst2 : ℕ
  p0 : ℕ
  p1 : ℕ
  p2 : ℕ
  U0 : ℕ
  U1 : ℕ
  U2 : ℕ
  J : ℕ
  src : ℕ
  NL : ℕ
  M : ℕ
  free : ℕ
  a : ℕ
  bank : ℕ
  powers : ℕ
  W : ℕ
  L : ℕ
  keyBase : ℕ
  valueBase : ℕ
  weightBase : ℕ
  weightU : ℕ
  factor : ℕ
  groups : ℕ
  U : ℕ
  input : ℕ→ℤ
  codes : ℕ→ℕ
  key : ℕ→ℕ
  group : ℕ→ℕ
def Setup.argv (S : Setup) : List ℤ :=
  LightTernarySourceCountHost.sourceArgs S.base0 S.dst0 S.base1 S.dst1 S.base2 S.dst2
    S.J S.p0 S.p1 S.p2 S.src S.NL S.M S.free S.a S.bank S.powers S.L
    S.keyBase S.valueBase S.weightBase S.factor S.groups
def Setup.records (S : Setup) : Finset (ℕ×ℕ) :=
  TernarySourceHostModel.records S.M S.NL (size S.xs S.J) S.input (dictionary S.xs S.p0 S.J)
def Setup.values {N : ℕ} (S : Setup) (enumeration : ℕ→TernaryJointType.TritWord N)
    (weight : ℕ→ℤ) (g : ℕ) (R : TernaryJointType.TritWord N) : ℤ :=
  TernaryConvolution.factorial R*TernarySourceHostModel.physical S.records enumeration
    S.key S.group weight g R
def Setup.runtime (S : Setup) : ℕ :=
  LightTernarySourceHost.time S.xs S.ys S.zs S.p0 S.J S.M S.NL S.U S.L S.bank S.groups S.input
structure Ready {N : ℕ} (S : Setup) (lim : Limits) (d : ℕ) (μ : ℕ→ℤ)
    (weight : ℕ→ℤ) (enumeration : ℕ→TernaryJointType.TritWord N) : Prop where
  hxy : S.ys.length=S.xs.length
  hxz : S.zs.length=S.xs.length
  hw : (lim.space : ℤ)≤lim.word
  hm : 0<S.xs.length
  hbase0 : S.base0+S.xs.length≤S.dst0
  hnext0 : LightRadixKeys.space S.dst0 S.xs.length S.J≤S.base1
  hbase1 : S.base1+S.xs.length≤S.dst1
  hnext1 : LightRadixKeys.space S.dst1 S.xs.length S.J≤S.base2
  hbase2 : S.base2+S.xs.length≤S.dst2
  hinitEnd : LightRadixKeys.space S.dst2 S.xs.length S.J≤S.free
  hsrc : S.src+S.NL≤S.base0
  hweights : S.weightBase+S.NL≤S.base0
  hbank : S.a+S.bank≤S.base0
  hpowerEnd : S.powers+(S.W+1)≤S.base0
  hkeyBase : LightWantedSetup.space S.free S.M S.input (dictionary S.xs S.p0 S.J)
      S.NL (size S.xs S.J) S.U 0 0≤S.keyBase
  hkeyEnd : S.keyBase+count S.xs S.p0 S.J S.M S.NL S.input≤S.valueBase
  hvalues : S.valueBase+S.groups*S.bank≤lim.space
  hb0 : ∀ x∈S.xs, |x|≤(S.U0 : ℤ)
  hb1 : ∀ x∈S.ys, |x|≤(S.U1 : ℤ)
  hb2 : ∀ x∈S.zs, |x|≤(S.U2 : ℤ)
  hw0 : (LightRadixKeys.word S.p0 S.U0 S.J : ℤ)≤lim.word
  hw1 : (LightRadixKeys.word S.p1 S.U1 S.J : ℤ)≤lim.word
  hw2 : (LightRadixKeys.word S.p2 S.U2 S.J : ℤ)≤lim.word
  hM : 0<S.M
  hjoinWord : (LightSourceResidues.word S.M S.M S.U 0 : ℤ)≤lim.word
  hlookupWord : ((S.bank+2^(S.W+1)+16 : ℕ) : ℤ)≤lim.word
  hgroupWord : ((S.groups*S.bank+1 : ℕ) : ℤ)≤lim.word
  hgroupSpace : S.groups*S.bank+1≤lim.space
  hfactor : (S.factor : ℤ)≤lim.word
  hweighted : (S.factor : ℤ)*(count S.xs S.p0 S.J S.M S.NL S.input*S.weightU : ℕ)≤lim.word
  hhistWord : ((count S.xs S.p0 S.J S.M S.NL S.input+1 : ℕ) : ℤ)*S.weightU≤lim.word
  hinput : ∀ i<S.NL, μ (S.src+i)=S.input i
  hinputBound : ∀ i<S.NL, |S.input i|≤(S.U : ℤ)
  hweightRead : ∀ i<S.NL, μ (S.weightBase+i)=weight i
  hweightBound : ∀ i<S.NL, |weight i|≤(S.weightU : ℤ)
  hglobal : S.U0*(S.p0+1)^S.J≤S.U
  hcodes : ∀ i<S.bank, μ (S.a+i)=(S.codes i : ℤ)
  hcodeBound : ∀ i<S.bank, S.codes i<2^S.W
  hpowers : Powers μ S.powers S.W
  hsorted : ∀ i k, i<k → k<S.bank → S.codes i<S.codes k
  hwordCode : ∀ j<size S.xs S.J, dictionary S.ys S.p1 S.J j=(S.codes (S.key j) : ℤ)
  hkey : ∀ j<size S.xs S.J, S.key j<S.bank
  hgroupCode : ∀ j<size S.xs S.J, dictionary S.zs S.p2 S.J j=(S.group j : ℤ)
  hgroup : ∀ j<size S.xs S.J, S.group j<S.groups
  hL : S.L≤S.W
  hn : S.bank<2^S.L
  hd : d+S.NL+S.L+S.J+8≤lim.depth
  hinjective : ∀ i j, i<S.bank → j<S.bank → enumeration i=enumeration j → i=j
  hfactorModel : ∀ pair∈S.records,
    (S.factor : ℤ)=TernaryConvolution.factorial (enumeration (S.key pair.2))
end ThreeSum.TernarySourceExecutionFactory


