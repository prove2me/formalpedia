-- Prove2me | solution 1 for AaronsonAmbainis.Average.variance_avg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:44:21.338876+00:00
-- url     : https://prove2.me/submissions/4d632bc9-61a5-42a5-87c5-057000fa537b

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Average_Coordinate
import Theorems.Thm_AaronsonAmbainis_Average_sum_flip
import Theorems.Thm_AaronsonAmbainis_Average_mean_avg

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Average
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Average
theorem _root_.solution (j : ι) (f : Cube ι → ℝ) :
    variance f = variance (avg j f) + inflR f j := by
  have hm := mean_avg j f
  have hre : ∑ x, (f (flipSet x {j}) - mean f) ^ 2 = ∑ x, (f x - mean f) ^ 2 :=
    sum_flip j (fun x => (f x - mean f) ^ 2)
  have hpt : ∀ x, (f x - mean f) ^ 2 + (f (flipSet x {j}) - mean f) ^ 2
      = 2 * ((avg j f x - mean f) ^ 2 + ((f x - f (flipSet x {j})) / 2) ^ 2) := by
    intro x
    unfold avg
    ring
  have hsum : ∑ x, (f x - mean f) ^ 2 + ∑ x, (f (flipSet x {j}) - mean f) ^ 2
      = 2 * (∑ x, (avg j f x - mean f) ^ 2 + ∑ x, ((f x - f (flipSet x {j})) / 2) ^ 2) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => hpt x)
  rw [hre] at hsum
  have hkey : ∑ x, (f x - mean f) ^ 2
      = ∑ x, (avg j f x - mean f) ^ 2 + ∑ x, ((f x - f (flipSet x {j})) / 2) ^ 2 := by
    linarith
  unfold variance inflR
  rw [hm, ← add_div, hkey]
end AaronsonAmbainis.Average
