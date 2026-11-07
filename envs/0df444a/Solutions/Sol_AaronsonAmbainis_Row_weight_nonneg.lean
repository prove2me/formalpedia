-- Prove2me | solution 1 for AaronsonAmbainis.Row.weight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:09:06.475271+00:00
-- url     : https://prove2.me/submissions/a3d5b3a6-e01b-4c58-a374-de334bcd5848

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Extension
import Theorems.Thm_AaronsonAmbainis_Row_abs_sgn


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.Row
theorem _root_.solution (u : ι → ℝ) (hu : ∀ i, |u i| ≤ 1) (z : Cube ι) : 0 ≤ weight u z := by
  refine Finset.prod_nonneg (fun i _ => ?_)
  have h1 : |sgn (z i) * u i| ≤ 1 := by
    rw [abs_mul, abs_sgn, one_mul]
    exact hu i
  have h2 := abs_le.mp h1
  linarith [h2.1]
end AaronsonAmbainis.Row
