-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem_of_isIntegral_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b8db8627-090b-5f45-b505-ccae21215e64

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem_of_isIntegral_mul

set_option autoImplicit false

universe u

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j j' : F) [Fact (j ≠ 0)] [Fact (j' ≠ 0)]
    (hb : ∃ a ∈ Algebra.adjoin R ({j⁻¹} : Set F), IsIntegral (Algebra.adjoin R ({j⁻¹} : Set F)) ((1 + j⁻¹ * a) * j'⁻¹)) :
    ∀ y ∈ chartAlgInf R F j', ∃ s ∈ chartAlgInf R F j,
      (∃ a ∈ chartAlgInf R F j, s = 1 + j⁻¹ * a) ∧ s * y ∈ chartAlgInf R F j := by
  classical
  obtain ⟨a, ha, hint⟩ := hb
  by_cases h0 : 1 + j⁻¹ * a = 0
  ·
    intro y _
    refine ⟨0, zero_mem _, ⟨a, adjoin_le_chartAlg R F _ ha, by rw [h0]⟩, ?_⟩
    rw [zero_mul]; exact zero_mem _
  ·
    apply AlgebraicCurve.TwoChartIntegralModel.forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem R F j j'
    refine ⟨a, ha, (1 + j⁻¹ * a)⁻¹, inv_mul_cancel₀ h0, ?_⟩
    have hle : Algebra.adjoin R ({j⁻¹} : Set F) ≤ Algebra.adjoin R ({j⁻¹, (1 + j⁻¹ * a)⁻¹} : Set F) :=
      Algebra.adjoin_mono (by simp)
    have h1 : IsIntegral (Algebra.adjoin R ({j⁻¹, (1 + j⁻¹ * a)⁻¹} : Set F)) ((1 + j⁻¹ * a) * j'⁻¹) :=
      hint.map_of_comp_eq (Subalgebra.inclusion hle).toRingHom (RingHom.id F) (by ext; rfl)
    have h2 : IsIntegral (Algebra.adjoin R ({j⁻¹, (1 + j⁻¹ * a)⁻¹} : Set F)) (1 + j⁻¹ * a)⁻¹ :=
      isIntegral_algebraMap (R := Algebra.adjoin R ({j⁻¹, (1 + j⁻¹ * a)⁻¹} : Set F))
        (x := (⟨(1 + j⁻¹ * a)⁻¹, Algebra.subset_adjoin (by simp)⟩ : Algebra.adjoin R ({j⁻¹, (1 + j⁻¹ * a)⁻¹} : Set F)))
    have h3 := h2.mul h1
    rwa [← mul_assoc, inv_mul_cancel₀ h0, one_mul] at h3

end S_AlgebraicCurve_TwoChartIntegralModel_forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem_of_isIntegral_mul
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem_of_isIntegral_mul (solution)
