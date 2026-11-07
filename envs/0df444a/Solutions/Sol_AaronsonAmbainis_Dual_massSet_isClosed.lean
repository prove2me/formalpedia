-- Prove2me | solution 1 for AaronsonAmbainis.Dual.massSet_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:39.239674+00:00
-- url     : https://prove2.me/submissions/4c81e471-0164-417b-9fd4-d6c2a5d28d1f

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Sets

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.Dual
theorem _root_.solution (K : ℝ) : IsClosed (massSet ι K) := by
  have h : massSet ι K = (⋂ i, {a : ι → ℝ | 0 ≤ a i}) ∩ {a : ι → ℝ | ∑ i, a i ≤ K} := by
    ext a
    simp [massSet]
  rw [h]
  exact IsClosed.inter
    (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i))
    (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
end AaronsonAmbainis.Dual
