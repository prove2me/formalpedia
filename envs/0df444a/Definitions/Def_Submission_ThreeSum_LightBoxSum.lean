-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBoxSum
-- name    : Submission_ThreeSum_LightBoxSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:47:47.487842+00:00
-- url     : https://prove2.me/theorems/6149ba6d-17e8-4788-b14c-e3e4a34dd18e
-- title:
--   Light Box Sum
-- statement:
--   Definitions and structural lemmas for Light Box Sum, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBoxSum.lean

import Definitions.Def_Submission_ThreeSum_LightQueryBox
import Definitions.Def_Submission_ThreeSum_BoxBounds
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightBoxSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def boxValue {L : ℕ} (Q : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (U : Finset (Fin L)) : ℤ := SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight
def partialSum {L : ℕ} (Q : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (missing : List (Finset (Fin L))) (j : ℕ) : ℤ :=
  ((missing.map (boxValue Q weight)).take j).sum
def roundBody (pBox : ℕ) : Stmt :=
  .call pBox [v 0,v 1,v 2,v 3,v 4,M (v 6 +' v 10),v 7,v 8] 11 ;;
  .set 9 (v 9 +' v 11)
def body (pBox : ℕ) : Stmt :=
  .set 9 (k 0) ;;
  .for 10 (v 5) (roundBody pBox) ;;
  .set 0 (v 9)
def time (L n : ℕ) : ℕ := n*(LightQueryBox.time L+60)+40
def Inv {L : ℕ} (μ : ℕ → ℤ) (Q : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (missing : List (Finset (Fin L))) (cut t maskBase base work j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,cut,Q.card,subsetMask Q,t,missing.length,maskBase,base,work,
      partialSum Q weight missing j,j,r],μ'⟩ ∧ Kept μ μ' work
def program : Program :=
  [body 1,LightQueryBox.body 2 3,LightMaskMinimum.body 9 12,LightStageLookup.body 4 5,
    LightDownsetSize.body 6 11,LightDownsetAddress.body 6 11,
    LightSubsetSetup.body 7 9 10,buildBody 8 13,fillBody,powTableBody,
    rankBody 10,LightSubsetOffset.body,LightMaskErase.body 12,rowBody 14,LightArray.linearBody]
end ThreeSum.LightBoxSum


