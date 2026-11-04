-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
-- name    : Submission_Weighted_Global_LightTernarySeedScoreFactory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T15:06:54.65185+00:00
-- url     : https://prove2.me/theorems/5e3f326d-a5ff-4374-8d8e-eccff65f3a0c
-- title:
--   Light Ternary Seed Score Factory
-- statement:
--   Definitions and structural lemmas for Light Ternary Seed Score Factory, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_SegN_read
import Theorems.Thm_Light_SolvesN_append
import Theorems.Thm_Light_Solves_append
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_SourceBucketView_read
import Theorems.Thm_ThreeSum_WeightedFrontendResources_controls
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedGlobalSeedScoreFactory
open Light
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
structure Config where
  menu : ℕ
  seed : ℕ
  J : ℕ
  catalog : ℕ
  catalogRows : ℕ
  p : ℕ
  power : ℕ
  Bmatrix : ℕ
  Bold : ℕ
  Bnew : ℕ
  nB : ℕ
  Cmatrix : ℕ
  Cold : ℕ
  Cnew : ℕ
  nC : ℕ
  Omatrix : ℕ
  Oold : ℕ
  Onew : ℕ
  nO : ℕ
  positions : ℕ
  wanted : ℕ
  work : ℕ
  hashWork : ℕ
  hist : ℕ
  header : ℕ
  leftTagged : ℕ
  rightTagged : ℕ
  leftWeights : ℕ
  rightWeights : ℕ
  tensor : ℕ
  countOutput : ℕ
  quadScratch : ℕ
  quadPowers : ℕ
  potentialColumns : ℕ
  potentialPowers : ℕ
  flags : ℕ
  scoreB : ℕ
  scoreC : ℕ
  scorePaired : ℕ
  prefixLength : ℕ
def Config.argv (C : Config) : List ℤ :=
  LightWeightedGlobalSeedScore.args C.menu C.seed C.J C.catalog C.catalogRows C.p C.power
    C.Bmatrix C.Bold C.Bnew C.nB C.Cmatrix C.Cold C.Cnew C.nC C.Omatrix C.Oold C.Onew C.nO
    C.positions C.wanted C.work C.hashWork C.hist C.header C.leftTagged C.rightTagged
    C.leftWeights C.rightWeights C.tensor C.countOutput C.quadScratch C.quadPowers
    C.potentialColumns C.potentialPowers C.flags C.scoreB C.scoreC C.scorePaired C.prefixLength
def Config.row (C : Config) := C.menu+C.seed*(C.J+2)
structure Data (C : Config) where
  oldB : ℕ → ℕ
  oldC : ℕ → ℕ
  oldO : ℕ → ℕ
  B : ℕ → ℕ → ℤ
  Cvalues : ℕ → ℕ → ℤ
  O : ℕ → ℕ → ℤ
  coeff : ℕ → ℕ
  position : ℕ → ℕ
  catalog : ℕ → ℕ → ℕ
  logicalRows : List (Fin C.J → ZMod C.p)
  logicalRow : Fin (C.J+2) → ZMod C.p
  bB : ℕ
  bC : ℕ
  bO : ℕ
def Data.newB {C : Config} (D : Data C) :=
  LightTernaryAppendKeys.key C.p C.power (C.J+2) D.oldB D.B D.coeff
def Data.newC {C : Config} (D : Data C) :=
  LightTernaryAppendKeys.key C.p C.power (C.J+2) D.oldC D.Cvalues D.coeff
def Data.newO {C : Config} (D : Data C) :=
  LightTernaryAppendKeys.key C.p C.power (C.J+2) D.oldO D.O D.coeff
def Data.targets {C : Config} (D : Data C) (i : ℕ) : ℤ := D.newO i
def Data.flag {C : Config} [Fact C.p.Prime] (D : Data C) : ℤ :=
  LightStoredSpan.admissibleFlag (D.logicalRows.map (TernaryPhysicalDigitSpan.reversal C.J))
    (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow)
def Data.collisionB {C : Config} (D : Data C) : ℤ :=
  (TernaryOriginalCollisions.collisionPairs (fun i : Fin C.nB => D.newB i.val)).card
def Data.collisionC {C : Config} (D : Data C) : ℤ :=
  (TernaryOriginalCollisions.collisionPairs (fun i : Fin C.nC => D.newC i.val)).card
def Data.wantedRows {C : Config} (D : Data C) (R S : ℕ) (raws : List ℤ) (words maps : List ℕ) :=
  LightTernaryWantedBatch.rows C.p R S C.prefixLength raws words maps D.targets D.position C.nO
def Data.H {C : Config} (D : Data C) (R S : ℕ) (raws : List ℤ) (words maps : List ℕ) :=
  TernaryWantedBatchCount.count C.p R S C.prefixLength raws words maps D.targets C.nO
def Reads (μ : ℕ → ℤ) (base n : ℕ) (f : ℕ → ℕ) := ∀i<n, μ (base+i)=(f i : ℤ)
def BuiltB (C : Config) (D : Data C) (μ ν : ℕ → ℤ) : Prop :=
  Kept μ ν C.Bnew ∧ Reads ν C.Bnew C.nB D.newB
def BuiltC (C : Config) (D : Data C) (μ ν : ℕ → ℤ) : Prop :=
  BuiltB C D μ ν ∧ Reads ν C.Cnew C.nC D.newC
def BuiltO (C : Config) (D : Data C) (μ ν : ℕ → ℤ) : Prop :=
  BuiltC C D μ ν ∧ Reads ν C.Onew C.nO D.newO
def Built (C : Config) (D : Data C) (R S : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (μ ν : ℕ → ℤ) : Prop :=
  BuiltO C D μ ν ∧ Seg ν C.wanted (D.wantedRows R S raws words maps)
structure AppendGuard (C : Config) (D : Data C) (lim : Limits) (depth : ℕ) (μ : ℕ → ℤ) : Prop where
  spaceWord : (lim.space : ℤ)≤lim.word
  depth : depth+4<lim.depth
  matrixB : C.Bmatrix+C.nB*(C.J+2)≤C.Bnew
  matrixC : C.Cmatrix+C.nC*(C.J+2)≤C.Bnew
  matrixO : C.Omatrix+C.nO*(C.J+2)≤C.Bnew
  rowBefore : C.row+(C.J+2)≤C.Bnew
  oldB : C.Bold+C.nB≤C.Bnew
  oldC : C.Cold+C.nC≤C.Bnew
  oldO : C.Oold+C.nO≤C.Bnew
  BC : C.Bnew+C.nB≤C.Cnew
  CO : C.Cnew+C.nC≤C.Onew
  outScratch : C.Onew+C.nO≤C.hashWork
  scratchSpace : C.hashWork+(C.J+2)≤lim.space
  bB : D.bB<C.p
  bC : D.bC<C.p
  bO : D.bO<C.p
  Bword : (LightTernaryAppendKeys.word (C.J+2) C.p D.bB C.power : ℤ)≤lim.word
  Cword : (LightTernaryAppendKeys.word (C.J+2) C.p D.bC C.power : ℤ)≤lim.word
  Oword : (LightTernaryAppendKeys.word (C.J+2) C.p D.bO C.power : ℤ)≤lim.word
  Bbound : ∀i<C.nB, ∀k<C.J+2, |D.B i k|≤(D.bB : ℤ)
  Cbound : ∀i<C.nC, ∀k<C.J+2, |D.Cvalues i k|≤(D.bC : ℤ)
  Obound : ∀i<C.nO, ∀k<C.J+2, |D.O i k|≤(D.bO : ℤ)
  coeffBound : ∀k<C.J+2, D.coeff k≤C.p
  oldBBound : ∀i<C.nB, D.oldB i<C.power
  oldCBound : ∀i<C.nC, D.oldC i<C.power
  oldOBound : ∀i<C.nO, D.oldO i<C.power
  BRead : ∀i<C.nB, ∀k<C.J+2, μ (C.Bmatrix+i*(C.J+2)+k)=D.B i k
  CRead : ∀i<C.nC, ∀k<C.J+2, μ (C.Cmatrix+i*(C.J+2)+k)=D.Cvalues i k
  ORead : ∀i<C.nO, ∀k<C.J+2, μ (C.Omatrix+i*(C.J+2)+k)=D.O i k
  coeffRead : ∀k<C.J+2, μ (C.row+k)=(D.coeff k : ℤ)
  oldBRead : Reads μ C.Bold C.nB D.oldB
  oldCRead : Reads μ C.Cold C.nC D.oldC
  oldORead : Reads μ C.Oold C.nO D.oldO
variable {lim : Limits}
structure SpanGuard (C : Config) [Fact C.p.Prime] (D : Data C) (lim : Limits) (μ : ℕ → ℤ) : Prop where
  represents : TernaryStoredSpan.Represents D.catalog C.catalogRows
    (D.logicalRows.map (TernaryPhysicalDigitSpan.reversal C.J))
  catalogSpace : C.catalog+C.J*C.catalogRows≤lim.space
  controls : ((C.catalogRows+C.J+16 : ℕ) : ℤ)≤lim.word
  pword : (C.p : ℤ)≤lim.word
  bounded : ∀k<C.catalogRows, ∀i<C.J, D.catalog k i<C.p
  read : ∀k<C.catalogRows, ∀i<C.J, μ (C.catalog+C.J*k+i)=(D.catalog k i : ℤ)
  digits : ∀i<C.J, D.coeff i=LightStoredSpan.rowValues
    (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow) i
structure WantedGuard (C : Config) (D : Data C) (lim : Limits) (depth R S cap V : ℕ)
    (raws : List ℤ) (words maps : List ℕ) (μ : ℕ → ℤ) : Prop where
  prime : 2≤C.p
  nonempty : 1≤raws.length
  Rpos : 1≤R
  Spos : 1≤S
  capPos : 1≤cap
  capBound : ∀x, (TernaryWantedRadix.localBucket (C.p : ℤ) raws x).length≤cap
  rawBound : ∀i<raws.length, |raws.getD i 0|≤(V : ℤ)
  wordBound : ∀i<raws.length, words.getD i 0<R
  mapBound : ∀i<raws.length, maps.getD i 0<S
  Rword : (R : ℤ)≤lim.word
  Sword : (S : ℤ)≤lim.word
  Nword : (raws.length : ℤ)≤lim.word
  division : Emod.Pre lim C.p (2*V) C.work
  targetEnd : C.Onew+C.nO≤C.wanted
  positionsEnd : C.positions+C.nO≤C.Bnew
  positionsRead : ∀i<C.nO, μ (C.positions+i)=(D.position i : ℤ)
  targetBound : ∀i<C.nO, |D.targets i|≤(V : ℤ)
  codesWord : (((2*R)^C.prefixLength : ℕ) : ℤ)≤lim.word
  mapsWord : (((2*S)^C.prefixLength : ℕ) : ℤ)≤lim.word
  positionsWord : ∀i<C.nO, (D.position i : ℤ)≤lim.word
  prefixWord : (C.prefixLength : ℤ)≤lim.word
  outputSpace : C.wanted+3*C.nO*cap^C.prefixLength≤C.work
  depth : depth+C.prefixLength+5≤lim.depth
structure CollisionGuard (C : Config) (D : Data C) (lim : Limits) (R S : ℕ)
    (raws : List ℤ) (words maps : List ℕ) : Prop where
  histogramAfter : C.wanted+(D.wantedRows R S raws words maps).length≤C.hist
  histogramSpace : C.hist+C.power*C.p≤lim.space
  Bword : ((C.nB*C.nB+C.nB+C.power*C.p+16 : ℕ) : ℤ)≤lim.word
  Cword : ((C.nC*C.nC+C.nC+C.power*C.p+16 : ℕ) : ℤ)≤lim.word
structure Ready (C : Config) [Fact C.p.Prime] (D : Data C) (lim : Limits)
    (depth R mapRadix cap V K N U : ℕ) (host : WeightedSourceCountExecutionFactory.Setup N)
    (L Rvalues : ℕ → ℕ → ℤ) (scoreBound : ℤ)
    (raws : List ℤ) (words maps : List ℕ) (μ : ℕ → ℤ) : Prop where
  append : AppendGuard C D lim depth μ
  span : SpanGuard C D lim μ
  wanted : WantedGuard C D lim depth R mapRadix cap V raws words maps μ
  collision : CollisionGuard C D lim R mapRadix raws words maps
  leftN : host.left.NL=C.nB
  rightN : host.right.NL=C.nC
  count : host.front.count=D.H R mapRadix raws words maps
  countOutput : host.front.dst=C.countOutput
  leftWeights : host.left.weightBase=C.leftWeights
  rightWeights : host.right.weightBase=C.rightWeights
  headerBefore : C.header+106≤C.Bnew
  tensorAfter : C.Bnew≤C.tensor
  tensor : ∀ν, Built C D R mapRadix raws words maps μ ν →
    LightWeightedGlobalTensorFactory.Ready host lim (depth+1) K C.J C.header C.leftTagged C.rightTagged
      C.tensor C.quadScratch C.quadPowers C.potentialColumns C.potentialPowers
      (Function.update ν (C.header+104) (D.H R mapRadix raws words maps : ℤ)) L Rvalues U scoreBound
  flagAddr : C.flags+C.seed<lim.space
  BAddr : C.scoreB+C.seed<lim.space
  CAddr : C.scoreC+C.seed<lim.space
  PAddr : C.scorePaired+C.seed<lim.space
  BWord : |D.collisionB|≤lim.word
  CWord : |D.collisionC|≤lim.word
  divideWord : ((3*D.H R mapRadix raws words maps+5 : ℕ) : ℤ)≤lim.word
def KeptInput (C : Config) (μ ν : ℕ → ℤ) : Prop :=
  ∀x<C.Bnew, x≠C.header+104 → ν x=μ x
def runtime {C : Config} (D : Data C) {N : ℕ} (host : WeightedSourceCountExecutionFactory.Setup N)
    (K R mapRadix cap V : ℕ) (raws : List ℤ) (words maps : List ℕ) : ℕ :=
  LightWeightedGlobalSeedScore.time (LightSpanCatalogTest.time C.J C.catalogRows)
    (LightTernaryAppendKeys.time C.nB (C.J+2) C.p D.bB)
    (LightTernaryAppendKeys.time C.nC (C.J+2) C.p D.bC)
    (LightTernaryAppendKeys.time C.nO (C.J+2) C.p D.bO)
    (LightTernaryWantedBatch.time C.p cap V C.prefixLength C.nO)
    (LightSmallDivide.time (3*D.H R mapRadix raws words maps) 3)
    (LightOriginalCollisionScore.time C.nB (C.power*C.p))
    (LightOriginalCollisionScore.time C.nC (C.power*C.p))
    (LightWeightedGlobalTensorDriver.time K C.J C.nB C.nC (D.H R mapRadix raws words maps) host.runtime)
open scoped BigOperators
end ThreeSum.LightWeightedGlobalSeedScoreFactory


