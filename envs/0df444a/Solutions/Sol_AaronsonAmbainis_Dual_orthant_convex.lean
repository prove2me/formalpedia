-- Prove2me | solution 1 for AaronsonAmbainis.Dual.orthant_convex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:59.607206+00:00
-- url     : https://prove2.me/submissions/c9bc1ee0-a946-4140-8533-9e0054fb4613

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Sets

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Dual
theorem _root_.solution : Convex ℝ (orthant ι) := by
  intro v hv w hw s r hs hr _ S
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg hs (hv S)) (mul_nonneg hr (hw S))
end AaronsonAmbainis.Dual
