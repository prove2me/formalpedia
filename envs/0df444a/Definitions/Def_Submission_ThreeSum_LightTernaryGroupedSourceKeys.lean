-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryGroupedSourceKeys
-- name    : Submission_ThreeSum_LightTernaryGroupedSourceKeys
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:34:18.55375+00:00
-- url     : https://prove2.me/theorems/eebc6a39-9501-4dee-bed1-f854e608a958
-- title:
--   Light Ternary Grouped Source Keys
-- statement:
--   Definitions and structural lemmas for Light Ternary Grouped Source Keys, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryGroupedSourceKeys.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightTernaryGroupedSourceKeys
open Light ThreeSum.LightSubsetAddress
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program}
def roundBody (pSearch : ℕ) : Stmt :=
  .call pSearch [v 0,v 1,M (v 6 +' M (v 4 +' k 2 *' v 11 +' k 1)),
    v 2,v 3,k 0] 12 ;;
  .store (v 8 +' v 11) (M (v 9 +' M (v 4 +' k 2 *' v 11 +' k 1)) *' v 1 +' v 12 -' k 1)
def body (pSearch : ℕ) : Stmt := .for 11 (v 5) (roundBody pSearch)
def time (L count : ℕ) : ℕ := count*(LightBandLookup.searchTime L+200)+20
def Inv (μ : ℕ → ℤ) (a bank powers L pairs count words wordCount dst groupBase groups : ℕ)
    (key group : ℕ → ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ r : ℤ, σ = ⟨frame [a,bank,powers,L,pairs,count,words,wordCount,dst,groupBase,groups,j,r],
    wrote μ dst (fun i => ((group i*bank+key i : ℕ) : ℤ)) j⟩
def program : Program := [body 1,LightBandLookup.searchBody 1]
end ThreeSum.LightTernaryGroupedSourceKeys


