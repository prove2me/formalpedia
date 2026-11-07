-- Prove2me | solution 1 for AaronsonAmbainis.antipodal_of_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:45.88165+00:00
-- url     : https://prove2.me/submissions/966734aa-4758-4ed3-93d0-0f906a420d34

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Antipodal
import Theorems.Thm_AaronsonAmbainis_wingSet_isWing
import Theorems.Thm_AaronsonAmbainis_wingSet_lower
import Theorems.Thm_AaronsonAmbainis_mem_zone


set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution : DetInequality → AntipodalInequality := by
  intro hDet ι _ _ g w hw lam hlam
  have key := hDet ι g (fun j => (w j)⁻¹) (fun j => inv_pos.mpr (hw j))
    (fun u => wingSet w (lam u) (lam (antipode u)))
    (fun u hu => wingSet_isWing (mem_zone.mp hu).1 hw (hlam u) (hlam (antipode u)).1)
    (fun u => (∑ j, w j * lam u j * lam (antipode u) j)⁻¹)
    (fun u hu G hG hgG =>
      wingSet_lower hw (hlam u).1 (hlam (antipode u)) (mem_zone.mp hu).2 G hG hgG)
  calc ∑ u ∈ zone g, (∑ j, w j * lam u j * lam (antipode u) j)⁻¹
      ≤ ∑ j, (w j)⁻¹ * (bdry g j : ℝ) := key
    _ = ∑ j, (bdry g j : ℝ) / w j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [div_eq_mul_inv, mul_comm]
end AaronsonAmbainis
