-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandEnumeration
-- name    : Submission_ThreeSum_LightBandEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:33:24.825858+00:00
-- url     : https://prove2.me/theorems/8a8e56a7-fdc5-4dda-9093-7db10a02318b
-- title:
--   Light Band Enumeration
-- statement:
--   Definitions and structural lemmas for Light Band Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandEnumeration.lean

import Definitions.Def_Submission_ThreeSum_LightBandTable
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_LightCapacity
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_ThreeSum_LightKaratsuba_program_procs

set_option autoImplicit false
namespace ThreeSum.LightBandEnumeration
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def At (μ : ℕ → ℤ) (lo hi : ℕ) (A : Family) : Prop :=
  (∀ i < A.size, μ (lo+i) = A.lower i) ∧
  (∀ i < A.size, μ (hi+i) = A.upper i)
def Bounded (A : Family) (U : ℕ) : Prop :=
  ∀ i < A.size, |A.lower i| ≤ (U : ℤ) ∧ |A.upper i| ≤ (U : ℤ)
def count (nA nB nC : ℕ) : ℕ := nB*nC+nA*nB+nA*nC
def width (nA nB nC : ℕ) : ℕ := Nat.clog 2 (nA+nB+nC+1)
def space (dst nA nB nC : ℕ) : ℕ := dst+count nA nB nC+width nA nB nC+1
def word (nA nB nC U : ℕ) : ℕ := 8*(nA+nB+nC+U+1)+32
def Tables (μ : ℕ → ℤ) (dst : ℕ) (A B C : Family) : Prop :=
  (∀ j < B.size, ∀ k < C.size,
    μ (dst+j*C.size+k) =
      (LightBandLookup.result A.lower A.upper A.size (C.lower k-B.upper j) : ℤ)) ∧
  (∀ i < A.size, ∀ j < B.size,
    μ (dst+B.size*C.size+i*B.size+j) =
      (LightBandLookup.result C.lower C.upper C.size (A.lower i+B.lower j) : ℤ)) ∧
  (∀ i < A.size, ∀ k < C.size,
    μ (dst+B.size*C.size+A.size*B.size+i*C.size+k) =
      (LightBandLookup.result B.lower B.upper B.size (C.lower k-A.lower i) : ℤ))
def body (pClog pPowers pTable : ℕ) : Stmt :=
  .set 10 (v 6 +' v 7 +' v 8) ;;
  .set 11 (v 7 *' v 8) ;;
  .set 12 (v 6 *' v 7) ;;
  .set 13 (v 6 *' v 8) ;;
  .set 14 (v 9 +' v 11) ;;
  .set 15 (v 14 +' v 12) ;;
  .set 16 (v 15 +' v 13) ;;
  .call pClog [v 10 +' k 1] 17 ;;
  .call pPowers [v 16,v 17 +' k 1,k 2] 18 ;;
  .call pTable [v 3,v 4,v 0,v 1,v 7,v 8,v 6,v 9,v 16,v 17,k 0 -' k 1] 18 ;;
  .call pTable [v 0,v 2,v 4,v 5,v 6,v 7,v 8,v 14,v 16,v 17,k 1] 18 ;;
  .call pTable [v 0,v 4,v 2,v 3,v 6,v 8,v 7,v 15,v 16,v 17,k 0 -' k 1] 18 ;;
  .set 0 (v 11 +' v 12 +' v 13)
def time (nA nB nC : ℕ) : ℕ :=
  clog2Time (nA+nB+nC+1)+powTableTime (width nA nB nC+1)+
    LightBandTable.time nB nC (width nA nB nC)+
    LightBandTable.time nA nB (width nA nB nC)+
    LightBandTable.time nA nC (width nA nB nC)+500
structure Procs (P : Program) (pMain : ℕ) where
  pClog : ℕ
  pPowers : ℕ
  pTable : ℕ
  pRow : ℕ
  pLookup : ℕ
  pSearch : ℕ
  main : P[pMain]? = some (body pClog pPowers pTable)
  clog : P[pClog]? = some clog2Body
  powers : P[pPowers]? = some powTableBody
  table : P[pTable]? = some (LightBandTable.body pRow)
  row : P[pRow]? = some (LightBandTable.rowBody pLookup)
  lookup : P[pLookup]? = some (LightBandLookup.body pSearch)
  search : P[pSearch]? = some (LightBandLookup.searchBody pSearch)
def program : Program :=
  [body 1 2 3,clog2Body,powTableBody,LightBandTable.body 4,
    LightBandTable.rowBody 5,LightBandLookup.body 6,LightBandLookup.searchBody 6]
def program_procs : Procs program 0 := ⟨1,2,3,4,5,6,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightBandEnumeration


