-- Prove2me | solution 1 for AddUN.Coding.branch_succ_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:24:54.104734+00:00
-- url     : https://prove2.me/submissions/1ee690d9-ae41-4cea-96a7-364670d85421

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding
variable {K : Set (ℕ → Bool)} {c : ℕ → Bool} {f : ℕ → ℕ} {n₀ : ℕ}
namespace AddUN.Coding
theorem _root_.solution {m : ℕ} (h : f (n₀ + m) ∉ bad K c (n₀ + m)) :
    branch K c f n₀ (m + 1) = branch K c f n₀ m ∩ hit c (n₀ + m) (f (n₀ + m)) := by
  rw [branch, if_neg h]
end AddUN.Coding
