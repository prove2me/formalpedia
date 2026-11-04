-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryTensorScatter
-- name    : Submission_ThreeSum_LightTernaryTensorScatter
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:22:00.356802+00:00
-- url     : https://prove2.me/theorems/9c3ed745-2ff5-48b8-a4da-7afa14c66696
-- title:
--   Light Ternary Tensor Scatter
-- statement:
--   Definitions and structural lemmas for Light Ternary Tensor Scatter, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryTensorScatter.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightTernaryTensorScatter
open Light
set_option maxHeartbeats 1800000
def body : Stmt := .for 5 (v 2) (.store (v 1 +' v 5 *' v 3 +' v 4) (M (v 0 +' v 5)))
def time (n : ℕ) : ℕ := 60*n+6
def Inv (μ : ℕ→ℤ) (src dst n W q i : ℕ) (σ : State) : Prop :=
  ∃ ν : ℕ→ℤ, σ=⟨frame [src,dst,n,W,q,i],ν⟩ ∧
    (∀ j<i, ν (dst+j*W+q)=μ (src+j)) ∧
    (∀ x, (∀ j<i, x≠dst+j*W+q)→ν x=μ x)
def program : Program := [body]
end ThreeSum.LightTernaryTensorScatter


