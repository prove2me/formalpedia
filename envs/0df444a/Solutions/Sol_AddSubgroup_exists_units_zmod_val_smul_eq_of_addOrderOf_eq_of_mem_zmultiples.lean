-- Prove2me | solution 1 for AddSubgroup.exists_units_zmod_val_smul_eq_of_addOrderOf_eq_of_mem_zmultiples
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/0ffae38c-6d73-5cab-8923-123e4394216d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddSubgroup_exists_units_zmod_val_smul_eq_of_addOrderOf_eq_of_mem_zmultiples

set_option autoImplicit false

theorem solution {G : Type*} [AddCommGroup G] (ℓ : ℕ) [NeZero ℓ] (P P' : G)
    (hP : addOrderOf P = ℓ) (hP' : addOrderOf P' = ℓ) (h : P' ∈ AddSubgroup.zmultiples P) :
    ∃ d : (ZMod ℓ)ˣ, P' = (d : ZMod ℓ).val • P := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp h
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ

  set n : ℕ := (k % ℓ).toNat with hn
  have hkn : k • P = n • P := by
    have hℓP : (ℓ : ℤ) • P = 0 := by
      rw [natCast_zsmul, ← hP]; exact addOrderOf_nsmul_eq_zero P
    have hnn : 0 ≤ k % ℓ := Int.emod_nonneg k hℓ0
    calc k • P = (ℓ * (k / ℓ) + k % ℓ) • P := by rw [Int.mul_ediv_add_emod]
      _ = (k / ℓ) • ((ℓ : ℤ) • P) + (k % ℓ) • P := by rw [add_zsmul, mul_comm, mul_zsmul]
      _ = (k % ℓ) • P := by rw [hℓP, zsmul_zero, zero_add]
      _ = n • P := by rw [hn, ← natCast_zsmul, Int.toNat_of_nonneg hnn]
  have hnlt : n < ℓ := by
    have := Int.emod_lt_of_pos k (Int.natCast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne ℓ)))
    omega

  have hcop : n.Coprime ℓ := by
    by_cases hn0 : n = 0
    ·
      rw [hkn, hn0, zero_smul, addOrderOf_zero] at hP'
      rw [hn0, ← hP']; exact Nat.coprime_one_right 0
    · have h1 := addOrderOf_nsmul' P hn0
      rw [← hkn, hP', hP] at h1
      have : Nat.gcd ℓ n = 1 := by
        rcases Nat.div_eq_self.mp h1.symm with h | h
        · exact absurd h (NeZero.ne ℓ)
        · exact h
      rw [Nat.coprime_comm]; exact this
  refine ⟨ZMod.unitOfCoprime n hcop, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hnlt, hkn]

end S_AddSubgroup_exists_units_zmod_val_smul_eq_of_addOrderOf_eq_of_mem_zmultiples
end P2MW
export P2MW.S_AddSubgroup_exists_units_zmod_val_smul_eq_of_addOrderOf_eq_of_mem_zmultiples (solution)
