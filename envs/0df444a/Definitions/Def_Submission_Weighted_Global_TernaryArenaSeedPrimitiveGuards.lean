-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedPrimitiveGuards
-- name    : Submission_Weighted_Global_TernaryArenaSeedPrimitiveGuards
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T21:17:58.119391+00:00
-- url     : https://prove2.me/theorems/3e02aa2b-4eb7-4744-a63f-9aa851a7d664
-- title:
--   Ternary Arena Seed Primitive Guards
-- statement:
--   Definitions and structural lemmas for Ternary Arena Seed Primitive Guards, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSeedPrimitiveGuards.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedScoreReady
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSeedPrimitiveGuards
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 8000000
def rawCap (m p r : ℕ) : ℕ :=p*(p+1)^r
def word (maps : Fin F→Weight m p) (τ : ℕ) (I : Input) (A : Inputs) (seed positionCap : ℕ)
    (D : Data (config p r I A seed)) : ℕ :=
  LightTernaryAppendKeys.word (A.J+2) p D.bB (p^(r-1))+
  LightTernaryAppendKeys.word (A.J+2) p D.bC (p^(r-1))+
  LightTernaryAppendKeys.word (A.J+2) p D.bO (p^(r-1))+
  p^(r-1)+A.J+16+p+(4^fixedLength m)+F+(WeightedGlobalGoodOutputCatalog.raws maps τ).length+
  (8*rawCap m p r+4*p+16)+(2*(4^fixedLength m))^r+(2*F)^r+positionCap+r+
  (I.nB*I.nB+I.nB+p^(r-1)*p+16)+(I.nC*I.nC+I.nC+p^(r-1)*p+16)
structure Reads (I : Input) (A : Inputs) (seed : ℕ) (D : Data (config p r I A seed))
    (μ : ℕ→ℤ) (positionCap : ℕ) : Prop where
  matrixB : A.Bmatrix+I.nB*(A.J+2)≤I.free
  matrixC : A.Cmatrix+I.nC*(A.J+2)≤I.free
  matrixO : A.Omatrix+I.requesterCount*(A.J+2)≤I.free
  menu : (config p r I A seed).row+(A.J+2)≤I.free
  positions : A.positions+I.requesterCount≤I.free
  bB : D.bB<p
  bC : D.bC<p
  bO : D.bO<p
  Bbound : ∀i<I.nB,∀k<A.J+2, |D.B i k|≤(D.bB : ℤ)
  Cbound : ∀i<I.nC,∀k<A.J+2, |D.Cvalues i k|≤(D.bC : ℤ)
  Obound : ∀i<I.requesterCount,∀k<A.J+2, |D.O i k|≤(D.bO : ℤ)
  coeffBound : ∀k<A.J+2, D.coeff k≤p
  oldB : ∀i<I.nB, D.oldB i<p^(r-1)
  oldC : ∀i<I.nC, D.oldC i<p^(r-1)
  oldO : ∀i<I.requesterCount, D.oldO i<p^(r-1)
  BRead : ∀i<I.nB,∀k<A.J+2, μ (A.Bmatrix+i*(A.J+2)+k)=D.B i k
  CRead : ∀i<I.nC,∀k<A.J+2, μ (A.Cmatrix+i*(A.J+2)+k)=D.Cvalues i k
  ORead : ∀i<I.requesterCount,∀k<A.J+2, μ (A.Omatrix+i*(A.J+2)+k)=D.O i k
  coeffRead : ∀k<A.J+2, μ ((config p r I A seed).row+k)=(D.coeff k : ℤ)
  oldBRead : LightWeightedGlobalSeedScoreFactory.Reads μ (addr I.free I.capacity 4) I.nB D.oldB
  oldCRead : LightWeightedGlobalSeedScoreFactory.Reads μ (addr I.free I.capacity 5) I.nC D.oldC
  oldORead : LightWeightedGlobalSeedScoreFactory.Reads μ (addr I.free I.capacity 6) I.requesterCount D.oldO
  represents : TernaryStoredSpan.Represents D.catalog (p^(r-1))
    (D.logicalRows.map (TernaryPhysicalDigitSpan.reversal A.J))
  catalogBound : ∀k<p^(r-1),∀i<A.J, D.catalog k i<p
  catalogRead : ∀k<p^(r-1),∀i<A.J, μ (addr I.free I.capacity 7+A.J*k+i)=(D.catalog k i : ℤ)
  digits : ∀i<A.J, D.coeff i=LightStoredSpan.rowValues (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow) i
  positionRead : ∀i<I.requesterCount, μ (A.positions+i)=(D.position i : ℤ)
  positionBound : ∀i<I.requesterCount, D.position i≤positionCap
end ThreeSum.WeightedGlobalArenaSeedPrimitiveGuards


