-- Prove2me | solution 1 for AaronsonAmbainis.Dual.slackImage_convex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:18.655334+00:00
-- url     : https://prove2.me/submissions/935992ee-f732-4776-b6c9-bd0768309978

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Sets
import Theorems.Thm_AaronsonAmbainis_Dual_massSet_convex

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.Dual
theorem _root_.solution (t : Finset ι → ℝ) (K : ℝ) :
    Convex ℝ (slack t '' massSet ι K) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ s r hs hr hsr
  refine ⟨s • a + r • b, massSet_convex K ha hb hs hr hsr, ?_⟩
  funext S
  simp only [slack, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  linear_combination (t S) * hsr
end AaronsonAmbainis.Dual
