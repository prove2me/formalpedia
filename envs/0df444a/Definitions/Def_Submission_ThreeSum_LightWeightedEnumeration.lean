-- Prove2me | Definitions.Def_Submission_ThreeSum_LightWeightedEnumeration
-- name    : Submission_ThreeSum_LightWeightedEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:41:51.299799+00:00
-- url     : https://prove2.me/theorems/4fc31e94-c7e3-4493-b54c-9aa89fef5aae
-- title:
--   Light Weighted Enumeration
-- statement:
--   Definitions and structural lemmas for Light Weighted Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightedEnumeration.lean

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_work_pos

set_option autoImplicit false
namespace ThreeSum.LightWeightedEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open LightSubsetEnumeration (time work_pos)
open scoped BigOperators
variable {lim : Limits} {P : Program}
def total (weights : ℕ → ℕ) (L : ℕ) : ℕ := ∑ i ∈ Finset.range L, weights i
def output (weights : ℕ → ℕ) : ℕ → ℕ → ℕ → List ℤ
  | _,0,pref => [pref]
  | 0,_+1,_ => []
  | L+1,k+1,pref =>
      if k+1 ≤ L+1 then
        output weights L (k+1) pref ++ output weights L k (pref+weights L)
      else []
def Weights (μ : ℕ → ℤ) (base W : ℕ) (weights : ℕ → ℕ) : Prop :=
  ∀ i, i < W → μ (base+i) = (weights i : ℤ)
def program : Program := [LightSubsetEnumeration.body 0]
end ThreeSum.LightWeightedEnumeration


