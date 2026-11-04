-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
-- name    : Submission_ThreeSum_LightTernaryMetadata
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:35:48.516937+00:00
-- url     : https://prove2.me/theorems/46a4931c-cb7c-405e-8e6d-e7400c9c3ff0
-- title:
--   Light Ternary Metadata
-- statement:
--   Definitions and structural lemmas for Light Ternary Metadata, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMetadata.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
namespace ThreeSum.LightTernaryMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}
def roundBody (pZero pDigit pErase : ℕ) : Stmt :=
  .set 8 (M (v 3 +' v 7)) ;;
  .call pZero [v 0,v 1,v 2,v 8,v 5] 9 ;;
  .call pErase [v 0,v 2,v 8,v 0,v 5] 10 ;;
  .call pDigit [v 0,v 1,v 2,v 8,v 5] 11 ;;
  .store (v 6 +' v 7) (v 11) ;;
  .store (v 6 +' v 4 +' v 7) (v 9) ;;
  .store (v 6 +' k 2 *' v 4 +' v 7) (v 10) ;;
  .store (v 6 +' k 3 *' v 4 +' v 7) (v 8)
def body (pZero pDigit pErase : ℕ) : Stmt :=
  .for 7 (v 4) (roundBody pZero pDigit pErase)
def roundTime (W : ℕ) : ℕ := LightTernaryCodes.zeroTime W +
  LightMaskErase.time W + LightTernaryCodes.digitTime W + 200
def time (W n : ℕ) : ℕ := n * (roundTime W + 20) + 20
def RecordAt (μ : ℕ → ℤ) (base n j W low high : ℕ) (m : ℕ) : Prop :=
  μ (base+j) = (LightTernaryCodes.digit W low high m : ℤ) ∧
  μ (base+n+j) = (LightTernaryCodes.zeroCode W low high m : ℤ) ∧
  μ (base+2*n+j) = (LightTernaryCodes.oneCode W high m : ℤ) ∧
  μ (base+3*n+j) = (m : ℤ)
noncomputable def writeRecord (μ : ℕ → ℤ) (base n j : ℕ) (q z0 z1 m : ℤ) : ℕ → ℤ :=
  Function.update (Function.update (Function.update (Function.update μ
    (base+j) q) (base+n+j) z0) (base+2*n+j) z1) (base+3*n+j) m
def Inv (μ : ℕ → ℤ) (W low high a n powers base : ℕ) (codes : ℕ → ℕ)
    (j : ℕ) (σ : State) : Prop :=
  ∃ (m z0 z1 q : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,low,high,a,n,powers,base,j,m,z0,z1,q],μ'⟩ ∧
    SameOutside μ μ' base (4*n) ∧
    ∀ k < j, RecordAt μ' base n k W low high (codes k)
def program : Program := [body 1 2 3, LightTernaryCodes.zeroBody 3,
  LightTernaryCodes.digitBody 3,LightMaskErase.body 3]
end ThreeSum.LightTernaryMetadata


