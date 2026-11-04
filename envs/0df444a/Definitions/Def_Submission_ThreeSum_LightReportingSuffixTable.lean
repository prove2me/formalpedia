-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingSuffixTable
-- name    : Submission_ThreeSum_LightReportingSuffixTable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:26:40.342923+00:00
-- url     : https://prove2.me/theorems/aa4f1bc5-7650-4dae-9d57-f8da29640b82
-- title:
--   Light Reporting Suffix Table
-- statement:
--   Definitions and structural lemmas for Light Reporting Suffix Table, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixTable.lean

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBatch
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightReportingSuffixTable
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostSuffix
variable {lim : Limits} {P : Program}
def enumBudget (V cut : ℕ) : ℕ := 800*(V+1)*(downsetCap V cut+1)
def batchBudget (W V cut : ℕ) : ℕ := 9400*(W+1)^2*(downsetCap V cut+1)
def roundBudget (W V cut : ℕ) : ℕ := enumBudget V cut+batchBudget W V cut+90
def roundBody (pEnumSetup pBatch : ℕ) : Stmt :=
  .call pEnumSetup [v 8,v 15,v 13,v 14] 16 ;;
  .call pBatch [v 0,v 1,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 15,v 16,v 13,
    v 10,v 11,v 12,v 14] 17
def body (pEnumSetup pBatch : ℕ) : Stmt :=
  .for 15 (v 2 +' k 1) (roundBody pEnumSetup pBatch)
def time (W V cut : ℕ) : ℕ := (cut+1)*(roundBudget W V cut+20)+20
def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ)
    (sourceCut boxCut stage baseL baseR dst maskBase work : ℕ)
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (n r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      V,2^offset,baseL,baseR,dst,maskBase,work,j,n,r],μ'⟩ ∧
    KeptBut μ μ' maskBase dst (downsetCap V boxCut) ∧
    TableAt μ' dst boxCut (LightSignedLeafTable.stageValues μ dst j (leafWeight hfit f g stage preL preR))
def program : Program := LightSignedBoxSetup.program ++
  [LightReportingSuffixCell.body 6 10,LightReportingSuffixBatch.body 25,body 3 26]
def procs : LightSignedLeafCell.Procs program 6 10 where
  pUnion := 7
  pLookup := 8
  pSign := 19
  pSize := 9
  pSetup := 11
  pBuild := 12
  pFill := 13
  pRow := 15
  pLinear := 24
  pPowers := 14
  pRank := 16
  pOffset := 17
  pErase := 18
  leaf := rfl
  union := rfl
  lookup := rfl
  sign := rfl
  size := rfl
  address := rfl
  setup := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  offset := rfl
  erase := rfl
end ThreeSum.LightReportingSuffixTable


