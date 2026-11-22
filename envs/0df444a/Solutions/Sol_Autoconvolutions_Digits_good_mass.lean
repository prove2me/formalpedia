-- Prove2me | solution 1 for Autoconvolutions.Digits.good_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:32.129302+00:00
-- url     : https://prove2.me/submissions/4ac3a674-c028-48f1-9473-fcbb5e04f11a

module
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_Digits
public import Theorems.Thm_Autoconvolutions_Digits_good_fraction

set_option autoImplicit true
@[expose] public section
public section
open Autoconvolutions Autoconvolutions.Digits
namespace Autoconvolutions.Digits
theorem _root_.solution {r b n u v : ℕ} (hn : 0 < n) (hb : 8*n^3 ≤ b)
    (hbr : b ≤ r) (huv : u + v = 4*n) :
    (1-1/(n : ℝ))*((r : ℝ)^u*(b : ℝ)^v) ≤
      (r.choose u : ℝ)*(b.choose v : ℝ)*(u.factorial : ℝ)*(v.factorial : ℝ) := by
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  have hr0 : 0 < r := lt_of_lt_of_le hb0 hbr
  have hbp : (0 : ℝ) < b := by exact_mod_cast hb0
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr0
  have hg := good_fraction hn hb hbr huv
  unfold distinctFraction at hg
  rw [div_mul_div_comm] at hg
  have h := (le_div_iff₀ (mul_pos (pow_pos hrp u) (pow_pos hbp v))).mp hg
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose] at h
  push_cast at h
  nlinarith only [h]
end Autoconvolutions.Digits
