-- Prove2me | Definitions.Def_Submission_ThreeSum_LightZetaPass
-- name    : Submission_ThreeSum_LightZetaPass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:36:09.08869+00:00
-- url     : https://prove2.me/theorems/6c342a84-f6d9-4358-9716-eb922fec193d
-- title:
--   Light Zeta Pass
-- statement:
--   Definitions and structural lemmas for Light Zeta Pass, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaPass.lean

import Definitions.Def_Submission_ThreeSum_LightZetaBatch
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightZetaPass
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def enumBudget (L cut : ℕ) : ℕ := 800*(L+1)*(downsetCap L cut+1)
def batchBudget (L cut : ℕ) : ℕ := 2100*(L+1)^2*(downsetCap L cut+1)
def roundBudget (L cut : ℕ) : ℕ := enumBudget L cut+batchBudget L cut+60
def roundBody (pEnumSetup pBatch : ℕ) : Stmt :=
  .call pEnumSetup [v 0,v 7,v 5,v 6] 8 ;;
  .call pBatch [v 0,v 7,v 8,v 5,v 2,v 3,v 4,v 6] 9
def body (pEnumSetup pBatch : ℕ) : Stmt :=
  .for 7 (v 1 +' k 1) (roundBody pEnumSetup pBatch)
def time (L cut : ℕ) : ℕ := (cut+1)*(roundBudget L cut+20)+20
def stageValues {L : ℕ} (μ : ℕ → ℤ) (dst j : ℕ)
    (a : Fin L) (f : Finset (Fin L) → ℤ) (S : Finset (Fin L)) : ℤ :=
  if S.card < j then Subset.zetaStep a f S else μ (dst+subsetRank S)
def Inv {L : ℕ} (μ : ℕ → ℤ) (cut src dst maskBase work : ℕ)
    (a : Fin L) (f : Finset (Fin L) → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (n r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,cut,a.val,src,dst,maskBase,work,j,n,r],μ'⟩ ∧
    KeptBut μ μ' maskBase dst (downsetCap L cut) ∧
    TableAt μ' dst cut (stageValues μ dst j a f)
def program : Program :=
  [body 1 2,LightSubsetEnumerationSetup.body 9 13,LightZetaBatch.body 3,
    LightZetaCell.body 4 11 12 10,LightSubsetSetup.body 5 9 10,
    buildBody 6 7,fillBody,rowBody 8,LightArray.linearBody,powTableBody,
    rankBody 10,LightSubsetOffset.body,LightMaskErase.body 12,LightSubsetEnumeration.body 13]
end ThreeSum.LightZetaPass


