-- Prove2me | solution 1 for Autoconvolutions.Estimate.norm_ratio_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:56:34.854471+00:00
-- url     : https://prove2.me/submissions/3b938fd9-e049-4ea2-b8f6-899ec794f9e1

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Definitions.Def_Autoconvolutions_Parameters
public import Definitions.Def_Autoconvolutions_Digits
public import Definitions.Def_Autoconvolutions_Levels
public import Definitions.Def_Autoconvolutions_Estimate
public import Theorems.Thm_Autoconvolutions_Estimate_height_pos
public import Theorems.Thm_Autoconvolutions_Estimate_plateau_sum_lower
public import Theorems.Thm_Autoconvolutions_Construction_card_evenAlphabet
public import Theorems.Thm_Autoconvolutions_Construction_card_oddAlphabet
attribute [local simp] Autoconvolutions.Construction.card_evenAlphabet
attribute [local simp] Autoconvolutions.Construction.card_oddAlphabet



set_option autoImplicit true
@[expose] public section
public section
open Finset
open Autoconvolutions Autoconvolutions.Estimate
namespace Autoconvolutions.Estimate
theorem _root_.solution {r b n K : ℕ} (hn : 0 < n) (hK : K ≤ n)
    (hb : 8*n^3 ≤ b) (hbr : b ≤ r) {square one peak : ℝ}
    (hOne : one = (((r:ℝ)*b)^n * ∑ s ∈ range (K+1), ((b:ℝ)/r)^s)^2)
    (hPeakPos : 0 < peak) (hPeak : peak ≤ height n (2*K))
    (hSq : (∑ s ∈ range (K+1), (s:ℝ)*count n r b s*(height n s)^2) ≤ square) :
    (1-1/(n:ℝ)) * Parameters.factorialRatio (2*n) (2*K) *
      Parameters.geomRatio ((b:ℝ)/r) K ≤ square/(one*peak) := by
  let q : ℝ := (b:ℝ)/r
  let S := ∑ s ∈ range (K+1), q^s
  let T := ∑ s ∈ range (K+1), (s:ℝ)*q^s
  let C := ((r:ℝ)*b)^n
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  have hr0 : 0 < r := lt_of_lt_of_le hb0 hbr
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hS : 0 < S := by
    have h := single_le_sum (f := fun s : ℕ => q^s) (fun s _ => pow_nonneg hq s)
      (a := 0) (by simp : 0 ∈ range (K+1))
    change 0 < ∑ s ∈ range (K+1), q^s
    exact lt_of_lt_of_le (by positivity) h
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hOne' : one = (C*S)^2 := hOne
  have hOnePos : 0 < one := hOne' ▸ (by positivity)
  have hfac : Parameters.factorialRatio (2*n) (2*K) = height n 0 / height n (2*K) := by
    simp [Parameters.factorialRatio, height, pow_two]
  rw [hfac]
  change (1-1/(n:ℝ))*(height n 0 / height n (2*K))*(T/S^2) ≤ _
  have hden : 0 < one*peak := mul_pos hOnePos hPeakPos
  apply (le_div_iff₀ hden).2
  have hf : 0 ≤ 1-1/(n:ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact_mod_cast hn
  have hE : 0 ≤ (1-1/(n:ℝ))*(height n 0 / height n (2*K))*(T/S^2) := by
    have h₀ := height_pos n 0
    have h₁ := height_pos n (2*K)
    positivity
  have hApos := height_pos n (2*K)
  calc
    _ ≤ (1-1/(n:ℝ))*(height n 0 / height n (2*K))*(T/S^2)*(one*height n (2*K)) := by gcongr
    _ = height n 0*(1-1/(n:ℝ))*((r:ℝ)*b)^(2*n)*T := by
      rw [hOne', show ((r:ℝ)*b)^(2*n) = C^2 by rw [Nat.mul_comm, pow_mul]]
      field_simp
    _ ≤ _ := (plateau_sum_lower hn hK hb hbr).trans hSq
end Autoconvolutions.Estimate
