-- Prove2me | solution 1 for AaronsonAmbainis.Row.eval_phi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:09:26.532228+00:00
-- url     : https://prove2.me/submissions/c860d668-d404-46c6-87da-4ee404d6b592

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Sensitivity

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {β : Type*} [Fintype β] [DecidableEq β]
namespace AaronsonAmbainis.Row
theorem _root_.solution (g : Finset β → ℝ) (R : Finset β) (s : ℝ) :
    (phi g R).eval s = ∑ U : Finset β, g U * ∏ b ∈ U, (if b ∈ R then 1 - s else 1) := by
  unfold phi
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl (fun U _ => ?_)
  rw [eval_mul, eval_C, eval_pow, eval_sub, eval_one, eval_X, Finset.prod_ite_mem,
    Finset.prod_const]
end AaronsonAmbainis.Row
