-- Prove2me | solution 1 for AlgebraicCurve.Divisor.mem_support_correspondence_single_iff_exists_and_iff_mem_support_correspondence_single
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/f2d13fec-3a2b-5e35-8153-604f1570c7c1

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_single
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_pos_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_mem_support_correspondence_single_iff_exists_and_iff_mem_support_correspondence_single

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfφ : FiniteAlong K φ) (hfψ : FiniteAlong K ψ) (P Q : Place K F) :
    (Q ∈ (Divisor.correspondence φ ψ hφ hψ (Finsupp.single P 1)).support ↔
        ∃ R : Place K F', R.restrictAlong φ hφ = P ∧ R.restrictAlong ψ hψ = Q) ∧
    (Q ∈ (Divisor.correspondence φ ψ hφ hψ (Finsupp.single P 1)).support ↔
        P ∈ (Divisor.correspondence ψ φ hψ hφ (Finsupp.single Q 1)).support) := by

  have key : ∀ (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
      (hfψ : FiniteAlong K ψ) (P Q : Place K F),
      Q ∈ (Divisor.correspondence φ ψ hφ hψ (Finsupp.single P 1)).support ↔
        ∃ R : Place K F', R.restrictAlong φ hφ = P ∧ R.restrictAlong ψ hψ = Q := by
    intro φ ψ hφ hψ hfψ P Q
    classical

    have he : ∀ R : Place K F', 0 < R.ramificationIndexAlong φ := fun R => by
      letI := algebraAlong φ
      haveI := isIntegral_along φ hφ
      exact R.ramificationIndex_pos
    have hf : ∀ R : Place K F', 0 < R.inertiaDegAlong ψ hψ := fun R => by
      letI := algebraAlong ψ
      haveI := isScalarTower_along ψ
      haveI : Module.Finite F F' := hfψ
      exact AlgebraicCurve.Place.inertiaDeg_pos_of_finiteDimensional R

    rw [Finsupp.mem_support_iff, AlgebraicCurve.Divisor.correspondence_single, Finsupp.coe_finset_sum, Finset.sum_apply]
    simp only [Finsupp.single_apply, one_mul]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    constructor
    · intro h
      obtain ⟨R, hR, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      rw [Finset.mem_filter, Place.mem_fiberAlong] at hR
      exact ⟨R, hR.1, hR.2⟩
    · rintro ⟨R, hRφ, hRψ⟩
      apply ne_of_gt
      apply Finset.sum_pos'
      · intro i _
        positivity
      · refine ⟨R, ?_, ?_⟩
        · rw [Finset.mem_filter, Place.mem_fiberAlong]; exact ⟨hRφ, hRψ⟩
        · exact mul_pos (Int.natCast_pos.mpr (he R)) (Int.natCast_pos.mpr (hf R))
  refine ⟨key φ ψ hφ hψ hfψ P Q, ?_⟩
  rw [key φ ψ hφ hψ hfψ P Q, key ψ φ hψ hφ hfφ Q P]
  exact ⟨fun ⟨R, h1, h2⟩ => ⟨R, h2, h1⟩, fun ⟨R, h1, h2⟩ => ⟨R, h2, h1⟩⟩

end S_AlgebraicCurve_Divisor_mem_support_correspondence_single_iff_exists_and_iff_mem_support_correspondence_single
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_mem_support_correspondence_single_iff_exists_and_iff_mem_support_correspondence_single (solution)
