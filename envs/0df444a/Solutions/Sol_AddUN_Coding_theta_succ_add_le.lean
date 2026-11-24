-- Prove2me | solution 1 for AddUN.Coding.theta_succ_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:39:00.343058+00:00
-- url     : https://prove2.me/submissions/c6c2c1ab-b58a-4400-bce9-34b0091407b9

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
theorem _root_.solution (n : ℕ) : theta (n + 1) + (1 / 2) ^ mu n ≤ theta n := by
  unfold theta
  rw [mu_succ, pow_mul']
  have hx0 : (0 : ℝ) < (1 / 2) ^ mu n := by positivity
  have hx1 : ((1 : ℝ) / 2) ^ mu n ≤ 1 / 2 := by
    calc ((1 : ℝ) / 2) ^ mu n ≤ (1 / 2) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.one_le_of_lt (lt_mu n))
      _ = 1 / 2 := by norm_num
  have h3 : (((1 : ℝ) / 2) ^ mu n) ^ 3 ≤ 1 / 8 := by
    calc (((1 : ℝ) / 2) ^ mu n) ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ hx0.le hx1 3
      _ = 1 / 8 := by norm_num
  nlinarith [mul_le_mul_of_nonneg_left h3 hx0.le]
end AddUN.Coding
