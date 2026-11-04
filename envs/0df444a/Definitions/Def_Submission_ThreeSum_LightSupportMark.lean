-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSupportMark
-- name    : Submission_ThreeSum_LightSupportMark
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:20:11.609398+00:00
-- url     : https://prove2.me/theorems/9dff8c06-91ce-46fc-a873-c5971ee390fb
-- title:
--   Light Support Mark
-- statement:
--   Definitions and structural lemmas for Light Support Mark, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSupportMark.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Finset.Range
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSupportMark
open Light Finset
def Hit (key valid : ℕ → ℕ) (r i : ℕ) : Prop :=
  ∃ j ∈ range i, valid j = 1 ∧ key j = r
instance (key valid : ℕ → ℕ) (r i : ℕ) : Decidable (Hit key valid r i) := by
  unfold Hit
  infer_instance
def bit (key valid : ℕ → ℕ) (r i : ℕ) : ℕ := if Hit key valid r i then 1 else 0
def markBody : Stmt :=
  .for 5 (v 3) (
    .ite (M (v 1 +' v 5) =' k 1)
      (.store (v 2 +' M (v 0 +' v 5)) (k 1)) .skip)
def markTime (n : ℕ) : ℕ := 40*n+6
variable {lim : Limits} {P : Program} {d : ℕ}
def body (pFill : ℕ) : Stmt :=
  .call pFill [v 2,v 4,k 0] 6 ;; markBody
def time (n p : ℕ) : ℕ := fillTime p+markTime n+10
def program : Program := [body 1,fillBody]
end ThreeSum.LightSupportMark


