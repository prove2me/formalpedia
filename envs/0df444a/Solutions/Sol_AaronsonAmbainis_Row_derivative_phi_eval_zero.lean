-- Prove2me | solution 1 for AaronsonAmbainis.Row.derivative_phi_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:11:15.728342+00:00
-- url     : https://prove2.me/submissions/b9daf216-cb23-493e-9a36-4de78801aa4f

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Sensitivity
import Theorems.Thm_AaronsonAmbainis_Row_sgn_false
import Theorems.Thm_AaronsonAmbainis_Row_sgn_true
attribute [local simp] AaronsonAmbainis.Row.sgn_false
attribute [local simp] AaronsonAmbainis.Row.sgn_true



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {β : Type*} [Fintype β] [DecidableEq β]
namespace AaronsonAmbainis.Row
theorem _root_.solution (g : Finset β → ℝ) (R : Finset β) :
    (phi g R).derivative.eval 0 = -∑ U : Finset β, g U * ((U ∩ R).card : ℝ) := by
  unfold phi
  rw [derivative_sum, eval_finsetSum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun U _ => ?_)
  rw [derivative_C_mul, derivative_pow, derivative_sub, derivative_one, derivative_X]
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_one, eval_X, eval_zero, sub_zero,
    one_pow]
  ring
end AaronsonAmbainis.Row
