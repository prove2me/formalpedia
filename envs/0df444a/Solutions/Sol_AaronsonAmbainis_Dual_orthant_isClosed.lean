-- Prove2me | solution 1 for AaronsonAmbainis.Dual.orthant_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:44:09.284908+00:00
-- url     : https://prove2.me/submissions/d8c60c17-682d-4923-a3a4-2b34beb92444

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Sets

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Dual
theorem _root_.solution : IsClosed (orthant ι) := by
  have h : orthant ι = ⋂ S : Finset ι, {v : Finset ι → ℝ | 0 ≤ v S} := by
    ext v
    simp [orthant]
  rw [h]
  exact isClosed_iInter fun S => isClosed_le continuous_const (continuous_apply S)
end AaronsonAmbainis.Dual
