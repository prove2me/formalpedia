-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryMomentMatrixInvariant
-- name    : Submission_ThreeSum_TernaryMomentMatrixInvariant
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:43:55.250061+00:00
-- url     : https://prove2.me/theorems/74fc07ce-7f32-4c76-acd2-520f2484c323
-- title:
--   Ternary Moment Matrix Invariant
-- statement:
--   Definitions and structural lemmas for Ternary Moment Matrix Invariant, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentMatrixInvariant.lean

import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentAccumulate
set_option autoImplicit false
namespace ThreeSum.TernaryMomentMatrixInvariant
open Light TernaryMomentSchedule
def Holds (reference : ℕ→ℤ) (matrix count terms boundary : ℕ)
    (done : List (ℕ×ℕ)) (score : ℕ→ℕ→ℕ→ℤ) (μ : ℕ→ℤ) : Prop :=
  (∀ k<terms, ∀ i<count, μ (matrix+k*count+i)=aggregate done score k i) ∧
  ∀ a<boundary, (a<matrix ∨ matrix+terms*count≤a) → μ a=reference a
end ThreeSum.TernaryMomentMatrixInvariant


