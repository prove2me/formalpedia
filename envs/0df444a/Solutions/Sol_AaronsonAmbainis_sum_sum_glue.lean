-- Prove2me | solution 1 for AaronsonAmbainis.sum_sum_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:28:59.886517+00:00
-- url     : https://prove2.me/submissions/054e4ce4-1086-4155-b309-8410d3ca7863

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
import Theorems.Thm_AaronsonAmbainis_card_cube


set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution (F : Finset ι) (φ : Cube ι → ℝ) :
    ∑ z, ∑ u, φ (glue F z u) = 2 ^ Fintype.card ι * ∑ x, φ x := by
  calc ∑ z, ∑ u, φ (glue F z u)
      = ∑ p : Cube ι × Cube ι, φ ((glueEquiv F p).1) :=
        (Fintype.sum_prod_type (fun p : Cube ι × Cube ι => φ ((glueEquiv F p).1))).symm
    _ = ∑ q : Cube ι × Cube ι, φ q.1 :=
        Equiv.sum_comp (glueEquiv F) (fun q : Cube ι × Cube ι => φ q.1)
    _ = ∑ x : Cube ι, ∑ _x' : Cube ι, φ x :=
        Fintype.sum_prod_type (fun q : Cube ι × Cube ι => φ q.1)
    _ = 2 ^ Fintype.card ι * ∑ x, φ x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_const, Finset.card_univ, card_cube, nsmul_eq_mul]
        push_cast
        ring
end AaronsonAmbainis
