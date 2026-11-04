-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSignedLeafTable
-- name    : Submission_ThreeSum_LightSignedLeafTable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:00:59.701065+00:00
-- url     : https://prove2.me/theorems/e8a894e6-5f48-4c84-8a45-f9d75d9f6c91
-- title:
--   Light Signed Leaf Table
-- statement:
--   Definitions and structural lemmas for Light Signed Leaf Table, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafTable.lean

import Definitions.Def_Submission_ThreeSum_LightSignedLeafBatch
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightSignedLeafTable
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def enumBudget (W cut : ℕ) : ℕ := 800*(W+1)*(downsetCap W cut+1)
def batchBudget (W cut : ℕ) : ℕ := 9400*(W+1)^2*(downsetCap W cut+1)
def roundBudget (W cut : ℕ) : ℕ := enumBudget W cut+batchBudget W cut+80
def roundBody (pEnumSetup pBatch : ℕ) : Stmt :=
  .call pEnumSetup [v 0,v 13,v 11,v 12] 14 ;;
  .call pBatch [v 0,v 1,v 3,v 4,v 5,v 6,v 7,v 13,v 14,v 11,v 8,v 9,v 10,v 12] 15
def body (pEnumSetup pBatch : ℕ) : Stmt :=
  .for 13 (v 2 +' k 1) (roundBody pEnumSetup pBatch)
def time (W cut : ℕ) : ℕ := (cut+1)*(roundBudget W cut+20)+20
def stageValues {W : ℕ} (μ : ℕ → ℤ) (dst j : ℕ)
    (weight : Finset (Fin W) → ℤ) (S : Finset (Fin W)) : ℤ :=
  if S.card < j then weight S else μ (dst+subsetRank S)
def Inv {W : ℕ} (μ : ℕ → ℤ) (sourceCut boxCut stage baseL baseR dst maskBase work : ℕ)
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (n r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      baseL,baseR,dst,maskBase,work,j,n,r],μ'⟩ ∧
    KeptBut μ μ' maskBase dst (downsetCap W boxCut) ∧
    TableAt μ' dst boxCut (stageValues μ dst j (SignedLeaf.value f g stage preL preR))
def program : Program :=
  [body 1 2,LightSubsetEnumerationSetup.body 12 18,LightSignedLeafBatch.body 3,
    LightSignedLeafCell.body 4 8,LightSignedLeafGeneral.body 5 6 17,LightMaskUnion.body 12 16,
    LightStageLookup.body 7 8,LightDownsetSize.body 9 15,LightDownsetAddress.body 9 15,
    LightSubsetSetup.body 10 12 14,buildBody 11 13,fillBody,powTableBody,rowBody 19,
    rankBody 14,LightSubsetOffset.body,LightMaskErase.body 16,LightSign.body,
    LightSubsetEnumeration.body 18,LightArray.linearBody]
def procs : LightSignedLeafCell.Procs program 4 8 where
  pUnion := 5
  pLookup := 6
  pSign := 17
  pSize := 7
  pSetup := 9
  pBuild := 10
  pFill := 11
  pRow := 13
  pLinear := 19
  pPowers := 12
  pRank := 14
  pOffset := 15
  pErase := 16
  leaf := rfl
  union := rfl
  lookup := rfl
  sign := rfl
  size := rfl
  address := rfl
  setup := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  offset := rfl
  erase := rfl
end ThreeSum.LightSignedLeafTable


