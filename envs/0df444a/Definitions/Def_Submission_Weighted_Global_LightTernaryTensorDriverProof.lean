-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryTensorDriverProof
-- name    : Submission_Weighted_Global_LightTernaryTensorDriverProof
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:15:33.285922+00:00
-- url     : https://prove2.me/theorems/18ec34de-8efd-4121-92b9-a5aa631a0b38
-- title:
--   Light Ternary Tensor Driver Proof
-- statement:
--   Definitions and structural lemmas for Light Ternary Tensor Driver Proof, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryTensorDriverProof.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorDriver
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedGlobalTensorDriver
open Light
open scoped BigOperators
set_option maxHeartbeats 4000000
def digit (J q i : ℕ) : ℕ := WeightEnumeration.digit (J+2) 4 q i
def InputKept (μ ν : ℕ→ℤ) (cut tensor H W : ℕ) : Prop := KeptBut μ ν cut tensor (H*W)
def Inv (μ : ℕ→ℤ) (vals : List ℤ) (J H tensor cut pow : ℕ)
    (T : ℕ→ℕ→ℤ) (q : ℕ) (σ : State) : Prop :=
  ∃ (powRet rowRet stepRet : ℤ) (ν : ℕ→ℤ),
    σ=⟨frame (vals++([J+2,(J+2)^4,powRet,q,rowRet,stepRet] : List ℤ)),ν⟩ ∧
    InputKept μ ν cut tensor H ((J+2)^4) ∧
    (∀ e≤4, ν (pow+e)=(((J+2)^e : ℕ) : ℤ)) ∧
    (∀ w<H, ∀ z<q, ν (tensor+w*((J+2)^4)+z)=T w z)
end ThreeSum.LightWeightedGlobalTensorDriver


