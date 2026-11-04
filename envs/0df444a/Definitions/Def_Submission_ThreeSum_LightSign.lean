-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSign
-- name    : Submission_ThreeSum_LightSign
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:20:34.042943+00:00
-- url     : https://prove2.me/theorems/ff0a441f-a2ef-4d49-91da-f8e46c38f9c2
-- title:
--   Light Sign
-- statement:
--   Definitions and structural lemmas for Light Sign, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSign.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSign
open Light
variable {lim : Limits} {P : Program}
def body : Stmt := .for 2 (v 1) (.set 0 (k 0 -' v 0))
def time (e : ℕ) : ℕ := 20*e+20
def Inv (μ : ℕ → ℤ) (x : ℤ) (e j : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [(-1 : ℤ)^j*x,e,j],μ⟩
def program : Program := [body]
end ThreeSum.LightSign


