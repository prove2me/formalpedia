-- Prove2me | Definitions.Def_Submission_ThreeSum_LightZetaStages
-- name    : Submission_ThreeSum_LightZetaStages
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:38:47.147416+00:00
-- url     : https://prove2.me/theorems/fa65665e-a382-403d-9fa5-54178e7080e4
-- title:
--   Light Zeta Stages
-- statement:
--   Definitions and structural lemmas for Light Zeta Stages, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaStages.lean

import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightZetaStages
open Light ThreeSum.SubsetAddress ThreeSum.SubsetStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def stageBase (base cap j : ℕ) : ℕ := base+j*cap
def StoredThrough {L : ℕ} (μ : ℕ → ℤ) (base cut : ℕ)
    (f : Finset (Fin L) → ℤ) (j : ℕ) : Prop :=
  ∀ i ≤ j, TableAt μ (stageBase base (downsetCap L cut) i) cut (stageValue f i)
def roundBody (pPass : ℕ) : Stmt :=
  .call pPass [v 0,v 1,v 0 -' k 1 -' v 6,
    v 2 +' v 6 *' v 5,v 2 +' (v 6 +' k 1) *' v 5,v 3,v 4] 7
def body (pSize pPass : ℕ) : Stmt :=
  .call pSize [v 0,v 1,v 4] 5 ;;
  .for 6 (v 0) (roundBody pPass)
def time (L cut : ℕ) : ℕ :=
  LightDownsetSize.time L+L*(LightZetaPass.time L cut+80)+80
def Inv {L : ℕ} (μ : ℕ → ℤ) (cut base maskBase work : ℕ)
    (f : Finset (Fin L) → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,cut,base,maskBase,work,downsetCap L cut,j,r],μ'⟩ ∧
    StoredThrough μ' base cut f j ∧
    KeptBut μ μ' maskBase base ((L+1)*downsetCap L cut)
def program : Program :=
  [body 1 2,LightDownsetSize.body 6 13,LightZetaPass.body 3 4,
    LightSubsetEnumerationSetup.body 11 15,LightZetaBatch.body 5,
    LightZetaCell.body 6 13 14 12,LightSubsetSetup.body 7 11 12,
    buildBody 8 9,fillBody,rowBody 10,LightArray.linearBody,powTableBody,
    rankBody 12,LightSubsetOffset.body,LightMaskErase.body 14,LightSubsetEnumeration.body 15]
end ThreeSum.LightZetaStages


