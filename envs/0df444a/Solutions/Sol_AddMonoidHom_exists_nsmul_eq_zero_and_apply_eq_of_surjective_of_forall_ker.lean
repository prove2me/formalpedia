-- Prove2me | solution 1 for AddMonoidHom.exists_nsmul_eq_zero_and_apply_eq_of_surjective_of_forall_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/aaf0c21e-7a2a-5e06-b6e5-f67956264069

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddMonoidHom_exists_nsmul_eq_zero_and_apply_eq_of_surjective_of_forall_ker

set_option autoImplicit false

theorem solution
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Surjective f)
    (m : ℕ) (hdiv : ∀ k : A, f k = 0 → ∃ j : A, f j = 0 ∧ m • j = k)
    (b : B) (hmb : m • b = 0) :
    ∃ a : A, m • a = 0 ∧ f a = b := by
  obtain ⟨a₀, ha₀⟩ := hf b
  have hker : f (m • a₀) = 0 := by rw [map_nsmul, ha₀, hmb]
  obtain ⟨j, hjker, hmj⟩ := hdiv (m • a₀) hker
  exact ⟨a₀ - j, by rw [smul_sub, hmj, sub_self], by rw [map_sub, ha₀, hjker, sub_zero]⟩

end S_AddMonoidHom_exists_nsmul_eq_zero_and_apply_eq_of_surjective_of_forall_ker
end P2MW
export P2MW.S_AddMonoidHom_exists_nsmul_eq_zero_and_apply_eq_of_surjective_of_forall_ker (solution)
