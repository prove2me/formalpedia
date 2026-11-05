-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorDriverProof
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorDriverProof
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:45:03.773196+00:00
-- url     : https://prove2.me/theorems/d4742da4-6595-4c5f-bd13-4958202d230a
-- title:
--   LightTernaryTensorDriverProof
-- statement:
--   Definitions and structural lemmas for LightTernaryTensorDriverProof, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryTensorDriverProof.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorDriver
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


