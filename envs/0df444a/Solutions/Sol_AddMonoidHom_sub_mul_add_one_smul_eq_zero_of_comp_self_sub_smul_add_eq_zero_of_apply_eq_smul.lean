-- Prove2me | solution 1 for AddMonoidHom.sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/3b13e494-ed5d-5c4d-bff5-14bc43d0f090

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddMonoidHom_sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul

set_option autoImplicit false

theorem solution
    {V : Type*} [AddCommGroup V] (m : V →+ V) (t : ℤ) (hm : ∀ T, m (m T) - t • m T + T = 0)
    (P : V) (c : ℤ) (hP : m P = c • P) :
    (c ^ 2 - t * c + 1) • P = 0 := by
  have h := hm P
  rw [hP, map_zsmul, hP, smul_smul] at h
  rw [add_smul, sub_smul, one_smul, mul_comm t c, sq, mul_smul, mul_smul] at *
  simpa [smul_smul, mul_comm] using h

end S_AddMonoidHom_sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul
end P2MW
export P2MW.S_AddMonoidHom_sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul (solution)
