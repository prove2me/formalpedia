-- Prove2me | Definitions.Def_Submission_ThreeSum_LightColoredTwoSum
-- name    : Submission_ThreeSum_LightColoredTwoSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:30:49.627048+00:00
-- url     : https://prove2.me/theorems/606a2f60-3d81-44f8-b1f8-5fdf128ddf25
-- title:
--   Light Colored Two Sum
-- statement:
--   Definitions and structural lemmas for Light Colored Two Sum, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColoredTwoSum.lean

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightColoredTwoSum
open Light ThreeSum.LightSubsetAddress
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
def Hit (scan target : ℕ → ℤ) (m j : ℕ) (bad sign : ℤ) : Prop :=
  ∃ i<j, ∃ k<m, target k=sign*scan i+bad
def flag (scan target : ℕ → ℤ) (m j : ℕ) (bad sign : ℤ) : ℕ :=
  if Hit scan target m j bad sign then 1 else 0
def roundBody (pLookup : ℕ) : Stmt :=
  .set 10 (v 7 *' M (v 0 +' v 9) +' v 6) ;;
  .call pLookup [v 2,v 2,v 3,v 10,v 4,v 5] 11 ;;
  .ite (k 0 <' v 11) (.set 8 (k 1)) .skip
def body (pLookup : ℕ) : Stmt := .set 8 (k 0) ;; .for 9 (v 1) (roundBody pLookup) ;; .set 0 (v 8)
def time (n L : ℕ) : ℕ := n*(LightBandLookup.time L+200)+100
def Inv (μ : ℕ → ℤ) (a n b m powers L : ℕ) (bad sign : ℤ) (scan target : ℕ → ℤ)
    (j : ℕ) (σ : State) : Prop := ∃ q r : ℤ,
    σ=⟨frame [a,n,b,m,powers,L,bad,sign,flag scan target m j bad sign,j,q,r],μ⟩
variable {lim : Limits} {P : Program}
def program : Program := [body 1,LightBandLookup.body 2,LightBandLookup.searchBody 2]
end ThreeSum.LightColoredTwoSum


