-- Prove2me | solution 1 for Autoconvolutions.Estimate.plateau_sum_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:46.866328+00:00
-- url     : https://prove2.me/submissions/bf9b35d8-4807-4100-900d-fda0c19a1c59

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Definitions.Def_Autoconvolutions_Parameters
public import Definitions.Def_Autoconvolutions_Digits
public import Definitions.Def_Autoconvolutions_Levels
public import Definitions.Def_Autoconvolutions_Estimate
public import Theorems.Thm_Autoconvolutions_Estimate_height_pos
public import Theorems.Thm_Autoconvolutions_Estimate_count_nonneg
public import Theorems.Thm_Autoconvolutions_Estimate_height_mono
public import Theorems.Thm_Autoconvolutions_Estimate_mass_lower

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Autoconvolutions Autoconvolutions.Estimate
namespace Autoconvolutions.Estimate
theorem _root_.solution {r b n K : ℕ} (hn : 0 < n) (hK : K ≤ n)
    (hb : 8*n^3 ≤ b) (hbr : b ≤ r) :
    height n 0 * (1-1/(n:ℝ)) * ((r:ℝ)*b)^(2*n) *
      (∑ s ∈ range (K+1), (s:ℝ) * ((b:ℝ)/r)^s) ≤
    ∑ s ∈ range (K+1), (s:ℝ) * count n r b s * (height n s)^2 := by
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro s hs
  have hs' : s ≤ 2*n := by have := mem_range.mp hs; omega
  have h := mass_lower hn hb hbr hs'
  have hh := height_mono (n := n) (i := 0) (Nat.zero_le s) hs'
  have hmin := mul_le_mul_of_nonneg_right hh (mul_nonneg (count_nonneg n r b s) (height_pos n s).le)
  calc
    _ = (s:ℝ) * (height n 0 * ((1-1/(n:ℝ)) * ((r:ℝ)*b)^(2*n) * ((b:ℝ)/r)^s)) := by ring
    _ ≤ (s:ℝ) * (height n 0 * (count n r b s * height n s)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (height_pos n 0).le) (by positivity)
    _ ≤ (s:ℝ) * (height n s * (count n r b s * height n s)) :=
      mul_le_mul_of_nonneg_left hmin (by positivity)
    _ = _ := by ring
end Autoconvolutions.Estimate
