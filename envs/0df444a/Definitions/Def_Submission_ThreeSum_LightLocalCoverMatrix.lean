-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalCoverMatrix
-- name    : Submission_ThreeSum_LightLocalCoverMatrix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:53:14.443654+00:00
-- url     : https://prove2.me/theorems/9f6465aa-3af2-4ce5-b872-fcb91e295be2
-- title:
--   Light Local Cover Matrix
-- statement:
--   Definitions and structural lemmas for Light Local Cover Matrix, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverMatrix.lean

import Definitions.Def_Submission_ThreeSum_LightLocalCoverCandidate
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightLocalCoverMatrix
open Light
set_option maxHeartbeats 2000000
set_option maxRecDepth 6000
def body (pCandidate : ℕ) : Stmt :=
  .set 16 (v 1 *' v 1) ;;
  .for 14 (v 2) (
    .call pCandidate [v 0,v 1,v 14,v 3,v 4,v 5,v 6,
      v 7 +' v 14 *' (k 2 *' v 0),v 8,v 9,
      v 10 +' v 14 *' v 1,v 11 +' v 14 *' v 1,v 12 +' v 14 *' v 16,v 13] 15)
def time (L n p N : ℕ) : ℕ := N*(LightLocalCoverCandidate.time L n p N+200)+30
def Tables (μ : ℕ → ℤ) (L n p cap maps hist0 hist1 dst : ℕ)
    (mask : ℕ → ℕ) (bits : ℕ → ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ j < N,
    LightWeightDecode.Rows μ (maps+j*(2*L)) L p j ∧
    (∀ r < p,
      μ (hist0+j*p+r) = (LightHistogram.count (LightHashHistogram.code L p mask (w0 j) (w1 j)) r n : ℤ) ∧
      μ (hist1+j*p+r) = (LightHistogram.count (LightHashHistogram.code L p mask (w1 j) (w0 j)) r n : ℤ)) ∧
    (∀ r < p*p, μ (dst+j*(p*p)+r) = (LightLocalCoverCandidate.entry L n p cap mask bits (w0 j) (w1 j) r : ℤ))
def Inv (μ : ℕ → ℤ) (L n p cap N masks bitPtr maps raw0 raw1 hist0 hist1 dst work : ℕ)
    (mask : ℕ → ℕ) (bits : ℕ → ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,p,N,n,cap,masks,bitPtr,maps,raw0,raw1,hist0,hist1,dst,work,i,r,p*p],μ'⟩ ∧
    Tables μ' L n p cap maps hist0 hist1 dst mask bits w0 w1 i ∧ Kept μ μ' maps
structure Procs (P : Program) (pMain : ℕ) where
  pCandidate : ℕ
  candidate : LightLocalCoverCandidate.Procs P pCandidate
  main : P[pMain]? = some (body pCandidate)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1,LightLocalCoverCandidate.body 2 7 14,LightWeightDecode.body 3 4,powTableBody,
    LightWeightRow.body 5,LightRadixDigit.body 6,LightSmallDivide.body,
    LightHashHistogram.body 8 10 12,LightMaskHashes.body 3 9,LightOneHot.body 9,
    LightResidues.residuesBody 11,emodBody,LightHistogram.histogramBody 13,fillBody,
    LightLocalCoverRow.body 15 18,LightPairFlags.body 6 16 17,LightBooleanDot.body,
    LightTrimTest.body,LightSupportMark.body 13]
def programProcs : Procs program 0 :=
  ⟨1,⟨2,7,14,⟨3,4,5,6,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨8,3,9,10,11,12,13,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨15,6,16,17,18,13,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩
end ThreeSum.LightLocalCoverMatrix


