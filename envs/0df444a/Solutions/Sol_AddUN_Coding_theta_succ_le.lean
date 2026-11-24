-- Prove2me | solution 1 for AddUN.Coding.theta_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:39:14.840938+00:00
-- url     : https://prove2.me/submissions/99517357-c7f9-401e-9c42-a35dff4bf76f

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_AddUN_Coding_mu_succ
public import Theorems.Thm_AddUN_Coding_lt_mu

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding
namespace AddUN.Coding
theorem _root_.solution (n : ℕ) : theta (n + 1) ≤ (1 / 2) ^ (mu n + n) / 2 * theta n := by
  unfold theta
  have h1 : ((1 : ℝ) / 2) ^ mu (n + 1) ≤ (1 / 2) ^ (mu n + n + mu n + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by
      rw [mu_succ]
      have := lt_mu n
      omega)
  rw [pow_succ, pow_add] at h1
  linarith
end AddUN.Coding
