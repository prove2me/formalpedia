-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources
-- name    : Submission_ThreeSum_TernaryPhysicalSources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:21:20.523206+00:00
-- url     : https://prove2.me/theorems/24329267-af99-4a82-96f8-3ac549762e3b
-- title:
--   Ternary Physical Sources
-- statement:
--   Definitions and structural lemmas for Ternary Physical Sources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalSources.lean

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
set_option autoImplicit false
namespace ThreeSum.TernaryPhysicalSources
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryConvolution
variable {ι κ : Type*}
noncomputable def histogram {N : ℕ} (S : Finset ι) (word : ι → TritWord N)
    (A : TritWord N) : ℤ :=
  ∑ i ∈ S, if word i=A then 1 else 0
noncomputable def pairCount {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι → TritWord N) (right : κ → TritWord N) (Q : TritWord N) : ℤ :=
  ∑ i ∈ S, ∑ j ∈ T, if Adds (left i) (right j) Q then 1 else 0
end ThreeSum.TernaryPhysicalSources


