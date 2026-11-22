-- Prove2me | solution 1 for Autoconvolutions.Digits.good_fraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:52.065064+00:00
-- url     : https://prove2.me/submissions/daa45336-204f-4d60-b9cd-f82b4e6b95cb

module
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_Digits
public import Theorems.Thm_Autoconvolutions_Digits_distinctFraction_nonneg
public import Theorems.Thm_Autoconvolutions_Digits_distinctFraction_le_one
public import Theorems.Thm_Autoconvolutions_Digits_collision_bound

set_option autoImplicit true
@[expose] public section
public section
open Autoconvolutions Autoconvolutions.Digits
namespace Autoconvolutions.Digits
theorem _root_.solution {r b n u v : ℕ} (hn : 0 < n) (hb : 8*n^3 ≤ b)
    (hbr : b ≤ r) (huv : u + v = 4*n) :
    1 - 1/(n : ℝ) ≤ distinctFraction r u * distinctFraction b v := by
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  have hr0 : 0 < r := lt_of_lt_of_le hb0 hbr
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb' : 8*(n : ℝ)^3 ≤ b := by exact_mod_cast hb
  have hbr' : (b : ℝ) ≤ r := by exact_mod_cast hbr
  have huv' : (u : ℝ) + v = 4*n := by exact_mod_cast huv
  have hu := sub_nonneg.mpr (distinctFraction_le_one hr0 u)
  have hv := sub_nonneg.mpr (distinctFraction_le_one hb0 v)
  have hpv := distinctFraction_nonneg b v
  have hboth : 0 ≤ 1 - distinctFraction r u * distinctFraction b v := by
    nlinarith only [hv, mul_nonneg hu hpv]
  have hcost : 2*(b : ℝ)*(1 - distinctFraction r u * distinctFraction b v)
      ≤ (4*(n : ℝ))^2 := by
    rw [← huv']
    nlinarith only [collision_bound hr0 u, collision_bound hb0 v,
      mul_nonneg (sub_nonneg.mpr hbr') hu,
      mul_nonneg (show (0 : ℝ) ≤ b by positivity) (mul_nonneg hu hv),
      mul_nonneg (show (0 : ℝ) ≤ u by positivity) (show (0 : ℝ) ≤ v by positivity)]
  have hnorm : (n : ℝ)*(1-distinctFraction r u*distinctFraction b v) ≤ 1 := by
    by_contra! hx
    have hpos := mul_pos (show (0 : ℝ) < 16*(n : ℝ)^2 by positivity) (sub_pos.mpr hx)
    nlinarith only [hcost, mul_nonneg (sub_nonneg.mpr hb') hboth, hpos]
  have hdiv : 1 - distinctFraction r u * distinctFraction b v ≤ 1/(n : ℝ) :=
    (le_div_iff₀ hn').2 (by simpa only [mul_comm (n : ℝ)] using hnorm)
  linarith
end Autoconvolutions.Digits
