-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernarySourceKeys
-- name    : Submission_ThreeSum_LightTernarySourceKeys
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:34:02.937175+00:00
-- url     : https://prove2.me/theorems/c4cd235d-58d2-4735-aa52-72a40fa28a0b
-- title:
--   Light Ternary Source Keys
-- statement:
--   Definitions and structural lemmas for Light Ternary Source Keys, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceKeys.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightTernarySourceKeys
open Light ThreeSum.LightSubsetAddress
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program}
def roundBody (pSearch : ℕ) : Stmt :=
  .call pSearch [v 0,v 1,M (v 6 +' M (v 4 +' k 2 *' v 9 +' k 1)),
    v 2,v 3,k 0] 10 ;;
  .store (v 8 +' v 9) (v 10 -' k 1)
def body (pSearch : ℕ) : Stmt := .for 9 (v 5) (roundBody pSearch)
def time (L count : ℕ) : ℕ := count*(LightBandLookup.searchTime L+200)+20
def Inv (μ : ℕ → ℤ) (a bank powers L pairs count words wordCount dst : ℕ)
    (key : ℕ → ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ r : ℤ, σ = ⟨frame [a,bank,powers,L,pairs,count,words,wordCount,dst,j,r],
    wrote μ dst (fun i => (key i : ℤ)) j⟩
def program : Program := [body 1,LightBandLookup.searchBody 1]
end ThreeSum.LightTernarySourceKeys


