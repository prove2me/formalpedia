-- Prove2me | solution 1 for Algebra.FormallySmooth.of_isRegularLocalRing_of_algHom_of_maximalIdeal_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/b823056f-7a9c-50c9-bc1f-0fa9147ddfb6

import Mathlib

import Definitions.Def_Mathlib_RingTheory_RegularLocalRingQuotientRegular
import Theorems.Thm_Algebra_FormallySmooth_of_isRegularLocalRing_of_surjective_algebraMap_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallySmooth_of_isRegularLocalRing_of_algHom_of_maximalIdeal_eq_span

set_option autoImplicit false

universe u

open IsLocalRing TensorProduct

theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (S : Type u) [CommRing S] [IsRegularLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Module.Flat R S]
    (ρ : S →ₐ[R] R) :
    Algebra.FormallySmooth R S := by
  classical

  set ϖS : S := algebraMap R S ϖ with hϖS
  have hI : (maximalIdeal R).map (algebraMap R S) = Ideal.span {ϖS} := by
    rw [hϖ, Ideal.map_span, Set.image_singleton]

  have hρsurj : Function.Surjective ρ := fun r => ⟨algebraMap R S r, ρ.commutes r⟩
  haveI : IsLocalHom ρ.toRingHom := IsLocalHom.of_surjective _ hρsurj
  have hρloc : ∀ x : S, x ∈ maximalIdeal S → ρ x ∈ maximalIdeal R := fun x hx =>
    map_nonunit ρ.toRingHom x hx

  have hregF : IsRegularLocalRing (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
    by_cases h0 : ϖ = 0
    · have hbot : (maximalIdeal R).map (algebraMap R S) = ⊥ := by
        rw [hI, Ideal.span_singleton_eq_bot, hϖS, h0, map_zero]
      exact IsRegularLocalRing.of_ringEquiv ((RingEquiv.quotientBot S).symm.trans (Ideal.quotEquivOfEq hbot.symm))
    · have hmem : ϖS ∈ maximalIdeal S := by
        apply map_nonunit (algebraMap R S) ϖ
        rw [hϖ]
        exact Ideal.subset_span rfl
      have hnot : ϖS ∉ (maximalIdeal S) ^ 2 := by
        intro h2
        have h3 : ρ ϖS ∈ (maximalIdeal R) ^ 2 := by
          have : ρ.toRingHom ϖS ∈ ((maximalIdeal S) ^ 2).map ρ.toRingHom := Ideal.mem_map_of_mem _ h2
          rw [Ideal.map_pow] at this
          exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr fun x hx => Ideal.mem_comap.mpr (hρloc x hx)) 2 this
        rw [hϖS, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, hϖ, Ideal.span_singleton_pow,
          Ideal.mem_span_singleton] at h3
        obtain ⟨a, ha⟩ := h3
        apply h0
        have hu : IsUnit (1 - ϖ * a) := by
          apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
          rw [← IsLocalRing.mem_maximalIdeal, hϖ]
          exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
        have hz : ϖ * (1 - ϖ * a) = 0 := by linear_combination ha
        exact (hu.mul_left_eq_zero).mp hz
      rw [hI]
      exact RegularQuotientEngine.isRegularLocalRing_quotient_span_singleton S hmem hnot
  haveI := hregF

  haveI hmax : (maximalIdeal R).IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  have hk : Function.Surjective
      (algebraMap (R ⧸ maximalIdeal R) (ResidueField (S ⧸ (maximalIdeal R).map (algebraMap R S)))) := by
    intro y
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨Ideal.Quotient.mk _ (ρ x), ?_⟩
    have hd : x - algebraMap R S (ρ x) ∈ maximalIdeal S := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have := (isUnit_map_iff ρ.toRingHom _).mpr hu
      simp at this
    have hx : x = algebraMap R S (ρ x) + (x - algebraMap R S (ρ x)) := by ring
    conv_rhs => rw [hx]
    rw [map_add, map_add]
    have hz : IsLocalRing.residue _ (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) (x - algebraMap R S (ρ x))) = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff]
      haveI := IsLocalHom.of_surjective (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S))) Ideal.Quotient.mk_surjective
      exact map_nonunit (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S))) _ hd
    rw [hz, add_zero]
    rfl
  have hF : Algebra.FormallySmooth (R ⧸ maximalIdeal R) (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    Algebra.FormallySmooth.of_isRegularLocalRing_of_surjective_algebraMap_residueField
      (R ⧸ maximalIdeal R) (S ⧸ (maximalIdeal R).map (algebraMap R S)) hk
  haveI : Algebra.FormallySmooth (R ⧸ maximalIdeal R) ((R ⧸ maximalIdeal R) ⊗[R] S) :=
    Algebra.FormallySmooth.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (maximalIdeal R))
  haveI : Algebra.FormallySmooth (ResidueField R) ((ResidueField R) ⊗[R] S) := ‹_›

  haveI : Algebra.FinitePresentation R (Algebra.EssFiniteType.subalgebra R S) :=
    (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (R := R) (S := S)
    (P := Algebra.EssFiniteType.subalgebra R S) (Algebra.EssFiniteType.submonoid R S)

end S_Algebra_FormallySmooth_of_isRegularLocalRing_of_algHom_of_maximalIdeal_eq_span
end P2MW
export P2MW.S_Algebra_FormallySmooth_of_isRegularLocalRing_of_algHom_of_maximalIdeal_eq_span (solution)
