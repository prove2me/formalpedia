-- Prove2me | solution 1 for AaronsonAmbainis.Row.gate_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:20:19.894216+00:00
-- url     : https://prove2.me/submissions/545166d2-d35b-4336-9e46-4d743c779b12

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget
import Theorems.Thm_AaronsonAmbainis_Row_cnt_unit

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
omit [Fintype ι]
namespace AaronsonAmbainis.Row
theorem _root_.solution [DecidableEq β] (S : β → Finset ι) (m : ℕ) (hm : 0 < m) (i : ι) (b : β) :
    gate S m (1 - Real.cos (Real.pi / (m : ℝ))) i (unit b) = if i ∈ S b then -1 else 1 := by
  unfold gate
  rw [cnt_unit]
  split_ifs with h
  · have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    have harg : ((m : ℤ) : ℝ) * (Real.pi / (m : ℝ)) = Real.pi := by
      push_cast
      field_simp
    rw [mul_one, sub_sub_cancel, Chebyshev.T_real_cos, harg, Real.cos_pi]
  · rw [mul_zero, sub_zero, Chebyshev.T_eval_one]
end AaronsonAmbainis.Row
