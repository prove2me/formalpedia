-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalCoverCandidate
-- name    : Submission_ThreeSum_LightLocalCoverCandidate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:50:00.151306+00:00
-- url     : https://prove2.me/theorems/80a0a387-0134-4bf0-8c5c-ede081cf3a16
-- title:
--   Light Local Cover Candidate
-- statement:
--   Definitions and structural lemmas for Light Local Cover Candidate, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverCandidate.lean

import Definitions.Def_Submission_ThreeSum_LightWeightDecode
import Definitions.Def_Submission_ThreeSum_LightLocalCoverHashHistogram
import Definitions.Def_Submission_ThreeSum_LightLocalCoverRow
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightLocalCoverCandidate
open Light
set_option maxHeartbeats 2000000
set_option maxRecDepth 6000
def body (pDecode pHash pRow : ℕ) : Stmt :=
  .call pDecode [v 0,v 1,v 2,v 7,v 13] 14 ;;
  .call pHash [v 0,v 5,v 8,v 8 +' v 3,v 10,v 3,v 7,v 7 +' v 0,v 1,v 13] 14 ;;
  .call pHash [v 0,v 5,v 9,v 9 +' v 3,v 11,v 3,v 7 +' v 0,v 7,v 1,v 13] 14 ;;
  .call pRow [v 6,v 8 +' v 3,v 9 +' v 3,v 10,v 11,v 12,v 3,v 0,v 1,v 4,v 13] 14
def time (L n p index : ℕ) : ℕ := LightWeightDecode.time L index+
  2*LightHashHistogram.time L n p p+LightLocalCoverRow.time L n p+200
def word (L n p cap index : ℕ) : ℕ := LightWeightDecode.word L p index+
  LightHashHistogram.word L p p+LightPairFlags.word L n p cap
def space (work L n p : ℕ) : ℕ :=
  work+2*(n*n)+(2*L+1)+max (L+1) (Nat.log 2 (L*p+1)+2)
def entry (L n p cap : ℕ) (mask : ℕ → ℕ) (bits : ℕ → ℕ → ℕ)
    (w0 w1 : ℕ → ℕ) (r : ℕ) : ℕ :=
  let left := LightHashHistogram.code L p mask w0 w1
  let right := LightHashHistogram.code L p mask w1 w0
  LightSupportMark.bit (LightPairFlags.pairKey n p left right)
    (LightPairFlags.pairFlag L n cap bits left right
      (fun r => LightHistogram.count left r n) (fun r => LightHistogram.count right r n)) r (n*n)
def Preserved (μ ν : ℕ → ℤ) (work coef raw0 raw1 hist0 hist1 dst L n p : ℕ) : Prop :=
  ∀ a, a < work → Outside coef (2*L) a → Outside raw0 (2*n) a → Outside raw1 (2*n) a →
    Outside hist0 p a → Outside hist1 p a → Outside dst (p*p) a → ν a = μ a
structure Procs (P : Program) (pMain : ℕ) where
  pDecode : ℕ
  pHash : ℕ
  pRow : ℕ
  decode : LightWeightDecode.Procs P pDecode
  hash : LightHashHistogram.Procs P pHash
  row : LightLocalCoverRow.Procs P pRow
  main : P[pMain]? = some (body pDecode pHash pRow)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 6 13,LightWeightDecode.body 2 3,powTableBody,LightWeightRow.body 4,
    LightRadixDigit.body 5,LightSmallDivide.body,LightHashHistogram.body 7 9 11,
    LightMaskHashes.body 2 8,LightOneHot.body 8,LightResidues.residuesBody 10,
    emodBody,LightHistogram.histogramBody 12,fillBody,LightLocalCoverRow.body 14 17,
    LightPairFlags.body 5 15 16,LightBooleanDot.body,LightTrimTest.body,LightSupportMark.body 12]
def programProcs : Procs program 0 :=
  ⟨1,6,13,⟨2,3,4,5,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨7,2,8,9,10,11,12,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨14,5,15,16,17,12,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩
end ThreeSum.LightLocalCoverCandidate


