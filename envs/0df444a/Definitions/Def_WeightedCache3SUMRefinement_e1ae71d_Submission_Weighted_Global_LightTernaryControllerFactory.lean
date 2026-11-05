-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryControllerFactory
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryControllerFactory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:31:13.322247+00:00
-- url     : https://prove2.me/theorems/7c1f97bf-ae95-43fe-b6b7-d065119959f5
-- title:
--   LightTernaryControllerFactory
-- statement:
--   Definitions and structural lemmas for LightTernaryControllerFactory, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryControllerFactory.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedController
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_SegN_read
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_Ready_next
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_Stored_next
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_SourceBucketView_read
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_Reads_update
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrontendResources_controls
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedGlobalControllerFactory
open Light LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
def withSeed (C : Config) (i : ℕ) : Config :={C with seed:=i}
instance {C : Config} [Fact C.p.Prime] (i : ℕ) : Fact (withSeed C i).p.Prime :=inferInstanceAs (Fact C.p.Prime)
structure Candidate (C : Config) [Fact C.p.Prime] where
  N : ℕ
  data : Data C
  host : WeightedSourceCountExecutionFactory.Setup N
  L : ℕ→ℕ→ℤ
  Rvalues : ℕ→ℕ→ℤ
  cap : ℕ
  V : ℕ
  U : ℕ
  scoreBound : ℤ
  leftRank : ℕ
  rightRank : ℕ
  twos : ℕ
  leftHom : ∀pair∈host.left.records, WeightedGlobalBank.rank (host.front.E.word (host.left.key pair.2))=leftRank
  rightHom : ∀pair∈host.right.records, WeightedGlobalBank.rank (host.front.E.word (host.right.key pair.2))=rightRank
  queryRank : ∀i<host.front.count, WeightedGlobalBank.rank (host.front.Q i)=leftRank+rightRank
  queryTwos : ∀i<host.front.count, TernaryJointType.digitCount (host.front.Q i) 2=twos
def Candidate.score {C : Config} [Fact C.p.Prime] (D : Candidate C) (K : ℕ) : ℤ :=
  ((2:ℤ)^D.twos)^K*(WeightedGlobalNativeTensorScore.pairedPotential D.host K C.J D.L D.Rvalues:ℤ)
def Candidate.runtime {C : Config} [Fact C.p.Prime] (D : Candidate C) (K R S : ℕ)
    (raws : List ℤ) (words maps : List ℕ) : ℕ :=
  LightWeightedGlobalSeedScoreFactory.runtime D.data D.host K R S D.cap D.V raws words maps
def Candidate.Guard {C : Config} [Fact C.p.Prime] (D : Candidate C) (lim : Limits)
    (depth K R S : ℕ) (raws : List ℤ) (words maps : List ℕ) (μ : ℕ→ℤ) : Prop :=
  Ready C D.data lim depth R S D.cap D.V K D.N D.U D.host D.L D.Rvalues D.scoreBound raws words maps μ ∧
    |D.score K|≤lim.word
def Candidate.Done {C : Config} [Fact C.p.Prime] (D : Candidate C) (K : ℕ) (μ ν : ℕ→ℤ) : Prop :=
  ∃ξ, KeptInput C μ ξ ∧ ν=
    Function.update (Function.update (Function.update (Function.update ξ
      (C.flags+C.seed) D.data.flag) (C.scoreB+C.seed) D.data.collisionB)
      (C.scoreC+C.seed) D.data.collisionC) (C.scorePaired+C.seed) (D.score K)
structure Family (C : Config) [Fact C.p.Prime] where
  candidate : (i : ℕ)→Candidate (withSeed C i)
  xl : List ℤ
  yl : List ℤ
  zl : List ℤ
  xr : List ℤ
  yr : List ℤ
  zr : List ℤ
  leftX : ∀i, (candidate i).host.left.xs=xl
  leftY : ∀i, (candidate i).host.left.ys=yl
  leftZ : ∀i, (candidate i).host.left.zs=zl
  rightX : ∀i, (candidate i).host.right.xs=xr
  rightY : ∀i, (candidate i).host.right.ys=yr
  rightZ : ∀i, (candidate i).host.right.zs=zr
def Family.flag {C : Config} [Fact C.p.Prime] (D : Family C) (i : ℕ) : ℤ :=(D.candidate i).data.flag
def Family.scoreB {C : Config} [Fact C.p.Prime] (D : Family C) (i : ℕ) : ℤ :=(D.candidate i).data.collisionB
def Family.scoreC {C : Config} [Fact C.p.Prime] (D : Family C) (i : ℕ) : ℤ :=(D.candidate i).data.collisionC
def Family.scoreP {C : Config} [Fact C.p.Prime] (D : Family C) (K i : ℕ) : ℤ :=(D.candidate i).score K
def Family.pick {C : Config} [Fact C.p.Prime] (D : Family C) (K n dB dC dP tB tC tP : ℕ) :=
  LightTernaryRowSelector.pick (LightTernaryRowSelector.Good D.flag D.scoreB D.scoreC (D.scoreP K)
    dB dC dP tB tC tP) n
structure SpanGuard (C : Config) [Fact C.p.Prime] (D : Data C) (lim : Limits)
    (depth newSpan : ℕ) (μ : ℕ→ℤ) : Prop where
  represents : TernaryStoredSpan.Represents D.catalog C.catalogRows
    (D.logicalRows.map (TernaryPhysicalDigitSpan.reversal C.J))
  rowsPos : 0<C.catalogRows
  spaceWord : (lim.space:ℤ)≤lim.word
  source : C.catalog+C.J*C.catalogRows≤newSpan
  row : C.row+C.J≤newSpan
  output : newSpan+C.J*C.catalogRows*C.p≤lim.space
  word : (LightPrimeCoefficient.word C.p:ℤ)≤lim.word
  controls : ((C.catalogRows+C.J+16:ℕ):ℤ)≤lim.word
  bounded : ∀k<C.catalogRows, ∀i<C.J, D.catalog k i<C.p
  read : ∀k<C.catalogRows, ∀i<C.J, μ (C.catalog+C.J*k+i)=(D.catalog k i:ℤ)
  rowRead : ∀i<C.J, μ (C.row+i)=
    (LightStoredSpan.rowValues (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow) i:ℤ)
  depth : depth+4≤lim.depth
def SpanDone (C : Config) [Fact C.p.Prime] (D : Data C) (newSpan : ℕ) (μ ν : ℕ→ℤ) : Prop :=
  (∀q<C.p*C.catalogRows, ∀i<C.J, ν (newSpan+C.J*q+i)=
    (TernaryStoredSpan.next D.catalog
      (LightStoredSpan.rowValues (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow))
      C.p C.catalogRows q i:ℤ)) ∧
  TernaryStoredSpan.Represents
    (TernaryStoredSpan.next D.catalog
      (LightStoredSpan.rowValues (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow)) C.p C.catalogRows)
    (C.p*C.catalogRows)
    (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow::D.logicalRows.map (TernaryPhysicalDigitSpan.reversal C.J)) ∧
  (∀q<C.p*C.catalogRows, ∀i<C.J, TernaryStoredSpan.next D.catalog
    (LightStoredSpan.rowValues (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow)) C.p C.catalogRows q i<C.p) ∧
  SameOutside μ ν newSpan (C.J*C.catalogRows*C.p)
end ThreeSum.LightWeightedGlobalControllerFactory
end
end WeightedCache3SUMRefinement_e1ae71d


