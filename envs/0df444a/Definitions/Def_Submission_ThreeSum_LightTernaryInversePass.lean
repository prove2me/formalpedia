-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
-- name    : Submission_ThreeSum_LightTernaryInversePass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:33:25.196302+00:00
-- url     : https://prove2.me/theorems/de2ab497-df7a-4eb8-bc7c-dffe0addf9b0
-- title:
--   Light Ternary Inverse Pass
-- statement:
--   Definitions and structural lemmas for Light Ternary Inverse Pass, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryInversePass.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightTernaryInversePass
set_option maxHeartbeats 2000000
open Light ThreeSum.TernaryQuery ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def roundBody (pCell : ℕ) : Stmt :=
  .call pCell [v 0,v 1,v 2,v 3,M (v 4 +' v 7),
    M (v 4 +' v 1 +' v 7),M (v 4 +' k 2 *' v 1 +' v 7),
    M (v 4 +' k 3 *' v 1 +' v 7),v 5] 8 ;;
  .store (v 6 +' v 7) (v 8)
def body (pCell : ℕ) : Stmt := .for 7 (v 1) (roundBody pCell)
def time (L n : ℕ) : ℕ := n * (LightTernaryLookup.time L + 100) + 20
def values (digits : ℕ → Fin 3) (ix : Fin 3 → ℕ → ℕ) (f : ℕ → ℤ) (j : ℕ) : ℤ :=
  inverseDigit (fun e => f (ix e j)) (digits j)
def Inv (μ : ℕ → ℤ) (a n powers L keyBase src dst : ℕ)
    (digits : ℕ → Fin 3) (ix : Fin 3 → ℕ → ℕ) (f : ℕ → ℤ)
    (j : ℕ) (σ : State) : Prop :=
  ∃ r : ℤ, σ = ⟨frame [a,n,powers,L,keyBase,src,dst,j,r],
    wrote μ dst (values digits ix f) j⟩
def program : Program := [body 1, LightTernaryLookup.body 2 3,
  LightBandLookup.searchBody 2, LightTernaryCell.inverseBody]
end ThreeSum.LightTernaryInversePass


