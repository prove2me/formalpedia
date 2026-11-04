-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSortedBands
-- name    : Submission_ThreeSum_LightSortedBands
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:35:58.573495+00:00
-- url     : https://prove2.me/theorems/6f1c5d3f-ecec-4910-bd51-84896aa2aeac
-- title:
--   Light Sorted Bands
-- statement:
--   Definitions and structural lemmas for Light Sorted Bands, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSortedBands.lean

import Definitions.Def_Submission_ThreeSum_LightNormalize
import Definitions.Def_Submission_ThreeSum_LightBandPartition
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store
import Theorems.Thm_ThreeSum_LightKaratsuba_program_procs

set_option autoImplicit false
namespace ThreeSum.LightSortedBands
open Light ThreeSum.BandPartition
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable {lim : Limits} {P : Program}
theorem getD_strict {L : List ℤ} (hs : L.Pairwise (· < ·)) :
    ∀ i j, i < j → j < L.length → L.getD i 0 < L.getD j 0 := by
  intro i j hij hj
  rw [List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ hj]
  exact List.pairwise_iff_getElem.mp hs i j (by omega) hj hij
def Prepared (μ : ℕ → ℤ) (values endpoints g : ℕ) (original : List ℤ) : Prop :=
  ∃ L : List ℤ,
    Seg μ values L ∧ L.Pairwise (· < ·) ∧ L.length ≤ original.length ∧
    (∀ z, z ∈ L ↔ z ∈ original) ∧
    μ endpoints = (L.length : ℤ) ∧ μ (endpoints+1) = (size L.length g : ℤ) ∧
    (∀ i < size L.length g, μ (endpoints+2+i) = L.getD (start g i) 0) ∧
    (∀ i < size L.length g, μ (endpoints+2+L.length+i) = L.getD (stop L.length g i-1) 0)
def body (pNormalize pPartition : ℕ) : Stmt :=
  .call pNormalize [v 0,v 1,v 3,v 5] 6 ;;
  .call pPartition [v 3,v 6,v 2,v 4 +' k 2] 7 ;;
  .store (v 4) (v 6) ;;
  .store (v 4 +' k 1) (v 7) ;;
  .set 0 (v 7)
def time (n : ℕ) : ℕ := LightNormalize.time n+200*n+300
def space (work n : ℕ) : ℕ := work+n
structure Procs (P : Program) (pMain : ℕ) where
  pNormalize : ℕ
  pPartition : ℕ
  pDivide : ℕ
  pLower : ℕ
  pUpper : ℕ
  normalize : LightNormalize.Procs P pNormalize
  partition : P[pPartition]? = some (LightBandPartition.body pDivide pLower pUpper)
  divide : P[pDivide]? = some LightSmallDivide.body
  lower : P[pLower]? = some LightBandPartition.lowerBody
  upper : P[pUpper]? = some LightBandPartition.upperBody
  main : P[pMain]? = some (body pNormalize pPartition)
def program : Program :=
  [body 1 7,LightNormalize.body 2 6,sortBody 2 3 4 5,halfBody,mergeBody,copyBody,
    LightNormalize.dedupBody 6,LightBandPartition.body 8 9 10,
    LightSmallDivide.body,LightBandPartition.lowerBody,LightBandPartition.upperBody]
def program_procs : Procs program 0 where
  pNormalize := 1
  pPartition := 7
  pDivide := 8
  pLower := 9
  pUpper := 10
  normalize := ⟨2,3,4,5,6,⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩
  partition := rfl
  divide := rfl
  lower := rfl
  upper := rfl
  main := rfl
theorem Prepared.family {μ : ℕ → ℤ} {values endpoints g : ℕ} {original : List ℤ}
    (h : Prepared μ values endpoints g original) (hg : 0 < g) :
    ∃ (L : List ℤ) (hs : L.Pairwise (· < ·)),
      Seg μ values L ∧ L.length ≤ original.length ∧ (∀ z, z ∈ L ↔ z ∈ original) ∧
      μ endpoints = (L.length : ℤ) ∧
      μ (endpoints+1) = (BandPartition.family (fun i => L.getD i 0) L.length g hg
        (getD_strict hs)).size ∧
      LightBandEnumeration.At μ (endpoints+2) (endpoints+2+L.length)
        (BandPartition.family (fun i => L.getD i 0) L.length g hg (getD_strict hs)) := by
  obtain ⟨L,hL,hs,hn,hmem,hlen,hcount,hlo,hhi⟩ := h
  exact ⟨L,hs,hL,hn,hmem,hlen,hcount,hlo,hhi⟩
end ThreeSum.LightSortedBands


