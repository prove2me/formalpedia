-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.variance_affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:16:04.06721+00:00
-- url     : https://prove2.me/submissions/8b8c9e93-743c-4dda-b92b-387b18694228

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Theorems.Thm_AaronsonAmbainis_Bridge_mean_affine

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (a b : ℝ) (g : Cube ι → ℝ) :
    variance (fun x => a + b * g x) = b ^ 2 * variance g := by
  have h : ∀ x : Cube ι, (a + b * g x - (a + b * mean g)) ^ 2 = b ^ 2 * (g x - mean g) ^ 2 :=
    fun x => by ring
  simp only [variance, mean_affine, h]
  rw [← Finset.mul_sum, mul_div_assoc]
end AaronsonAmbainis.Bridge
