-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
-- name    : Submission_ThreeSum_TernaryWeightedPhysicalSources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:27:42.404117+00:00
-- url     : https://prove2.me/theorems/c02955c7-9a2d-4cc9-badc-6ad733d7a1e4
-- title:
--   Ternary Weighted Physical Sources
-- statement:
--   Definitions and structural lemmas for Ternary Weighted Physical Sources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightedPhysicalSources.lean

import Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryWeightedPhysicalSources
open Finset TernaryJointType TernaryBank TernaryConvolution
open scoped BigOperators
variable {ι κ : Type*}
def histogram {N : ℕ} (S : Finset ι) (word : ι → TritWord N)
    (weight : ι → ℤ) (A : TritWord N) : ℤ :=
  ∑ i ∈ S, if word i=A then weight i else 0
def pairWeight {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι → TritWord N) (right : κ → TritWord N)
    (leftWeight : ι → ℤ) (rightWeight : κ → ℤ) (Q : TritWord N) : ℤ :=
  ∑ i ∈ S, ∑ j ∈ T,
    if Adds (left i) (right j) Q then leftWeight i*rightWeight j else 0
end ThreeSum.TernaryWeightedPhysicalSources


