-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandPreprocessing
-- name    : Submission_ThreeSum_LightBandPreprocessing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:42:13.319324+00:00
-- url     : https://prove2.me/theorems/5592ddb5-e1cc-4a42-8268-09bc4bd14d1e
-- title:
--   Light Band Preprocessing
-- statement:
--   Definitions and structural lemmas for Light Band Preprocessing, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPreprocessing.lean

import Definitions.Def_Submission_ThreeSum_LightHeaderBands
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_ThreeSum_LightKaratsuba_program_procs

set_option autoImplicit false
namespace ThreeSum.LightBandPreprocessing
open Light ThreeSum.BandPartition
set_option maxHeartbeats 1800000
set_option maxRecDepth 5000
variable {lim : Limits} {P : Program}
def Represents (μ : ℕ → ℤ) (values endpoints g : ℕ) (hg : 0 < g)
    (original L : List ℤ) (hs : L.Pairwise (· < ·)) : Prop :=
  Seg μ values L ∧ L.length ≤ original.length ∧ (∀ z, z ∈ L ↔ z ∈ original) ∧
    LightHeaderBands.At μ endpoints L.length
      (family (fun i => L.getD i 0) L.length g hg (LightSortedBands.getD_strict hs))
def Output (μ : ℕ → ℤ) (av ae bv be cv ce dst g : ℕ) (hg : 0 < g)
    (originalA originalB originalC : List ℤ) (r : ℤ) : Prop :=
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·))
    (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
      r = (LightBandEnumeration.count (size A.length g) (size B.length g) (size C.length g) : ℤ) ∧
      Represents μ av ae g hg originalA A hsA ∧
      Represents μ bv be g hg originalB B hsB ∧
      Represents μ cv ce g hg originalC C hsC ∧
      LightBandEnumeration.Tables μ dst
        (family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA))
        (family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB))
        (family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC))
def body (pPrepare pEnumerate : ℕ) : Stmt :=
  .call pPrepare [v 0,v 1,v 6,v 7,v 8,v 13] 14 ;;
  .call pPrepare [v 2,v 3,v 6,v 9,v 10,v 13] 14 ;;
  .call pPrepare [v 4,v 5,v 6,v 11,v 12,v 13] 14 ;;
  .call pEnumerate [v 8,v 10,v 12,v 13] 0
def time (a b c g : ℕ) : ℕ :=
  LightSortedBands.time a+LightSortedBands.time b+LightSortedBands.time c+
    LightHeaderBands.time (size a g) (size b g) (size c g)+300
def space (work a b c g : ℕ) : ℕ :=
  work+(a+b+c)+LightBandEnumeration.count (size a g) (size b g) (size c g)+
    LightBandEnumeration.width (size a g) (size b g) (size c g)+1
def word (a b c g U : ℕ) : ℕ :=
  a+b+c+g+2+LightBandEnumeration.word (size a g) (size b g) (size c g) U
def depth (a b c g : ℕ) : ℕ :=
  a+b+c+Nat.clog 2 (a+b+c)+
    LightBandEnumeration.width (size a g) (size b g) (size c g)+10
structure Procs (P : Program) (pMain : ℕ) where
  pPrepare : ℕ
  pEnumerate : ℕ
  prepare : LightSortedBands.Procs P pPrepare
  enumerate : LightHeaderBands.Procs P pEnumerate
  main : P[pMain]? = some (body pPrepare pEnumerate)
def program : Program :=
  [body 1 12,
    LightSortedBands.body 2 8,LightNormalize.body 3 7,
    sortBody 3 4 5 6,halfBody,mergeBody,copyBody,LightNormalize.dedupBody 7,
    LightBandPartition.body 9 10 11,LightSmallDivide.body,
    LightBandPartition.lowerBody,LightBandPartition.upperBody,
    LightHeaderBands.body 13,LightBandEnumeration.body 14 15 16,clog2Body,powTableBody,
    LightBandTable.body 17,LightBandTable.rowBody 18,LightBandLookup.body 19,LightBandLookup.searchBody 19]
def program_procs : Procs program 0 where
  pPrepare := 1
  pEnumerate := 12
  prepare := ⟨2,8,9,10,11,⟨3,4,5,6,7,⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl⟩
  enumerate := ⟨13,⟨14,15,16,17,18,19,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩
  main := rfl
end ThreeSum.LightBandPreprocessing


