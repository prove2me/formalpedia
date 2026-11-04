-- Prove2me | Definitions.Def_Submission_ThreeSum_LightMaskMinimum
-- name    : Submission_ThreeSum_LightMaskMinimum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:30:52.999265+00:00
-- url     : https://prove2.me/theorems/14dfa499-fd7c-4d48-a7fe-1ab445f22864
-- title:
--   Light Mask Minimum
-- statement:
--   Definitions and structural lemmas for Light Mask Minimum, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskMinimum.lean

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Mathlib.Data.Finset.Max
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
namespace ThreeSum.LightMaskMinimum
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def best {L : ℕ} (S : Finset (Fin L)) (hS : S.Nonempty) (j : ℕ) : ℕ :=
  if (S.min' hS).val < j then (S.min' hS).val else L
def roundBody (pErase : ℕ) : Stmt :=
  .call pErase [v 0,v 5,v 1,v 0,v 2] 6 ;;
  .ite (v 6 <' v 1) (.ite (v 5 <' v 4) (.set 4 (v 5)) .skip) .skip
def body (pPowers pErase : ℕ) : Stmt :=
  .call pPowers [v 2,v 0 +' k 1,k 2] 3 ;;
  .set 4 (v 0) ;;
  .for 5 (v 0) (roundBody pErase) ;;
  .set 0 (v 4)
def time (L : ℕ) : ℕ := powTableTime (L+1)+L*(LightMaskErase.time L+100)+100
def Inv {L : ℕ} (μ : ℕ → ℤ) (S : Finset (Fin L)) (hS : S.Nonempty)
    (work : ℕ) (powRet : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ r : ℤ, σ = ⟨frame [L,subsetMask S,work,powRet,best S hS j,j,r],μ⟩
def program : Program := [body 1 2,powTableBody,LightMaskErase.body 2]
end ThreeSum.LightMaskMinimum


