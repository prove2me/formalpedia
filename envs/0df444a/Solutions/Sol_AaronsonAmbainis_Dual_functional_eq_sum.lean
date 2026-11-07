-- Prove2me | solution 1 for AaronsonAmbainis.Dual.functional_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:48:08.371571+00:00
-- url     : https://prove2.me/submissions/31d4642c-1af1-4a8c-a541-70ef64b351b7

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Functional
import Theorems.Thm_AaronsonAmbainis_Dual_eq_sum_single

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {β : Type*} [Fintype β] [DecidableEq β]
namespace AaronsonAmbainis.Dual
theorem _root_.solution (φ : (β → ℝ) →L[ℝ] ℝ) (v : β → ℝ) :
    φ v = ∑ b, φ (Pi.single b 1) * v b := by
  conv_lhs => rw [eq_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
end AaronsonAmbainis.Dual
