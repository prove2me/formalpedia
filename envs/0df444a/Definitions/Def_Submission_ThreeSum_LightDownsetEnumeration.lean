-- Prove2me | Definitions.Def_Submission_ThreeSum_LightDownsetEnumeration
-- name    : Submission_ThreeSum_LightDownsetEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:32:46.545535+00:00
-- url     : https://prove2.me/theorems/23589000-9159-46ff-af5b-467f63fd2498
-- title:
--   Light Downset Enumeration
-- statement:
--   Definitions and structural lemmas for Light Downset Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetEnumeration.lean

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightDownsetEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def layers (L : ℕ) : ℕ → List ℕ
  | 0 => []
  | j+1 => layers L j ++ enumerateLayer L j
def budget (L cut : ℕ) : ℕ := 150*((4*L+1)*downsetCap L cut+1)
def roundBody (pEnum : ℕ) : Stmt :=
  .call pEnum [v 0,v 4,k 0,v 2 +' v 5,v 3] 6 ;;
  .set 5 (v 5 +' v 6)
def body (pEnum : ℕ) : Stmt :=
  .set 5 (k 0) ;;
  .for 4 (v 1 +' k 1) (roundBody pEnum) ;;
  .set 0 (v 5)
def time (L cut : ℕ) : ℕ := (cut+1)*(budget L cut+70)+40
def Inv (μ : ℕ → ℤ) (L cut dst powers j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,cut,dst,powers,j,layerOffset L j,r],μ'⟩ ∧
    SegN μ' dst (layers L j) ∧ SameOutside μ μ' dst (layerOffset L j)
def program : Program := [body 1,LightSubsetEnumeration.body 1]
end ThreeSum.LightDownsetEnumeration


