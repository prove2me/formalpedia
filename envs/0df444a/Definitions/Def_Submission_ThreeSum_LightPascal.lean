-- Prove2me | Definitions.Def_Submission_ThreeSum_LightPascal
-- name    : Submission_ThreeSum_LightPascal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:20:35.203238+00:00
-- url     : https://prove2.me/theorems/7a81605a-a165-440b-bca2-2b721f06418b
-- title:
--   Light Pascal
-- statement:
--   Definitions and structural lemmas for Light Pascal, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPascal.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Nat.Choose.Bounds
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightPascal
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
def tableSize (L : ℕ) : ℕ := (L+1)^2
def Table (μ : ℕ → ℤ) (dst L : ℕ) : Prop :=
  ∀ i ≤ L, ∀ j ≤ L, μ (dst + i*(L+1) + j) = (i.choose j : ℤ)
def rowBody (pLinear : ℕ) : Stmt :=
  .call pLinear [v 0, v 0 +' k 1, v 1 +' k 1, v 2, k 1] 3 ;;
  .store (v 1) (k 1)
def rowTime (L : ℕ) : ℕ := LightArray.linearTime L + 20
def buildBody (pFill pRow : ℕ) : Stmt :=
  .set 2 (v 1 +' k 1) ;;
  .call pFill [v 0,v 2,k 0] 4 ;;
  .store (v 0) (k 1) ;;
  .for 3 (v 1) (
    .call pRow [v 0 +' v 3 *' v 2,
      v 0 +' (v 3 +' k 1) *' v 2, v 1] 4)
def buildTime (L : ℕ) : ℕ := fillTime (L+1) + L*(rowTime L+100)+100
def Inv (μ : ℕ → ℤ) (dst L i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [dst,L,L+1,i,r],μ'⟩ ∧
    (∀ a ≤ i, ∀ j ≤ L, μ' (dst+a*(L+1)+j) = (a.choose j : ℤ)) ∧
      SameOutside μ μ' dst (tableSize L)
end ThreeSum.LightPascal


