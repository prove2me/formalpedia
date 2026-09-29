-- Prove2me | solution 1 for AddCircle.exists_eq_coe_div_of_nsmul_eq_zero_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/cb738001-c48a-5493-a993-e105b45437c6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddCircle_exists_eq_coe_div_of_nsmul_eq_zero_of_dvd

set_option autoImplicit false

theorem solution
    (t : AddCircle (1 : ℚ)) (n N : ℕ) (hN : 0 < N) (hnN : n ∣ N) (ht : n • t = 0) :
    ∃ a : ℤ, t = (((a : ℚ) / (N : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
  have hn : n ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hnN
    omega
  induction t using QuotientAddGroup.induction_on with
  | H q =>

    have hq : ((n • q : ℚ) : AddCircle (1 : ℚ)) = 0 := by rw [AddCircle.coe_nsmul]; exact ht
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℚ)).mp hq
    obtain ⟨d, hd⟩ := hnN
    refine ⟨k * d, ?_⟩
    congr 1
    rw [zsmul_eq_mul, mul_one, nsmul_eq_mul] at hk
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [eq_div_iff hN', hd]
    push_cast
    rw [hk]
    ring

end S_AddCircle_exists_eq_coe_div_of_nsmul_eq_zero_of_dvd
end P2MW
export P2MW.S_AddCircle_exists_eq_coe_div_of_nsmul_eq_zero_of_dvd (solution)
