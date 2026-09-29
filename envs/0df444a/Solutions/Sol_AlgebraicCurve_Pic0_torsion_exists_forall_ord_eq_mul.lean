-- Prove2me | solution 1 for AlgebraicCurve.Pic0.torsion.exists_forall_ord_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/136e4f7d-4a9e-5401-8a84-121d334368a8

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_torsion_exists_forall_ord_eq_mul

set_option Elab.async false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (x : Pic0.torsion K F n) (D : Divisor.degZero (K := K) (F := F)) (hD : Pic0.mk D = (x : Pic0 K F)) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v := by
  have hx : (n : ℤ) • (x : Pic0 K F) = 0 := Pic0.mem_torsion.mp x.2
  have h1 : Pic0.mk ((n : ℤ) • D) = 0 := by
    have h2 : Pic0.mk ((n : ℤ) • D) = (n : ℤ) • Pic0.mk D := by
      show QuotientAddGroup.mk ((n : ℤ) • D) = (n : ℤ) • (QuotientAddGroup.mk D)
      exact QuotientAddGroup.mk_zsmul
        ((Divisor.principal (K := K) (F := F)).addSubgroupOf
          (Divisor.degZero (K := K) (F := F))) D (n : ℤ)
    rw [h2, hD, hx]
  have h3 : ((n : ℤ) • D : Divisor.degZero (K := K) (F := F)) ∈
      (Divisor.principal (K := K) (F := F)).addSubgroupOf
        (Divisor.degZero (K := K) (F := F)) :=
    (QuotientAddGroup.eq_zero_iff _).mp h1
  rw [AddSubgroup.mem_addSubgroupOf] at h3
  have h4 : Divisor.IsPrincipal ((n : ℤ) • (D : Divisor K F)) := Divisor.mem_principal.mp h3
  obtain ⟨f, hf0, hford⟩ := h4
  refine ⟨f, hf0, fun v => ?_⟩
  have := hford v
  rw [Finsupp.smul_apply, smul_eq_mul] at this
  exact this.symm

end

end S_AlgebraicCurve_Pic0_torsion_exists_forall_ord_eq_mul
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_torsion_exists_forall_ord_eq_mul (solution)
