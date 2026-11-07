-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.variance_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:34:20.798784+00:00
-- url     : https://prove2.me/submissions/55f12ff2-c484-4926-9ca0-73c89df8748a

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Theorems.Thm_AaronsonAmbainis_Bridge_card_cube
import Theorems.Thm_AaronsonAmbainis_Level_card_cube
import Theorems.Thm_AaronsonAmbainis_Level_variance_le_sq_dist
import Theorems.Thm_AaronsonAmbainis_card_cube


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {f : Cube ι → ℝ} (h : ∀ x, |f x| ≤ 1) : variance f ≤ 1 := by
  have hpos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  refine (Level.variance_le_sq_dist f 0).trans ?_
  rw [div_le_iff₀ hpos]
  have h1 : ∑ x : Cube ι, (f x - 0) ^ 2 ≤ ∑ _x : Cube ι, (1 : ℝ) :=
    Finset.sum_le_sum (fun x _ => by
      have h2 := abs_le.mp (h x)
      have h3 : 0 ≤ 1 - f x := by linarith [h2.2]
      have h4 : 0 ≤ 1 + f x := by linarith [h2.1]
      nlinarith [mul_nonneg h3 h4])
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube] at h1
  linarith
end AaronsonAmbainis.Bridge
