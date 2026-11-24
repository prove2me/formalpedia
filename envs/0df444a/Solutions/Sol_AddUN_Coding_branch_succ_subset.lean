-- Prove2me | solution 1 for AddUN.Coding.branch_succ_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:39:32.294903+00:00
-- url     : https://prove2.me/submissions/4a62d46b-b606-457e-8fe3-af6e771fe80e

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_AddUN_Coding_branch_succ_of_mem
public import Theorems.Thm_AddUN_Coding_branch_succ_of_notMem

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding
variable {K : Set (ℕ → Bool)} {c : ℕ → Bool} {f : ℕ → ℕ} {n₀ : ℕ}
namespace AddUN.Coding
theorem _root_.solution (m : ℕ) : branch K c f n₀ (m + 1) ⊆ branch K c f n₀ m := by
  by_cases h : f (n₀ + m) ∈ bad K c (n₀ + m)
  · rw [branch_succ_of_mem h]
    exact sdiff_subset
  · rw [branch_succ_of_notMem h]
    exact inter_subset_left
end AddUN.Coding
