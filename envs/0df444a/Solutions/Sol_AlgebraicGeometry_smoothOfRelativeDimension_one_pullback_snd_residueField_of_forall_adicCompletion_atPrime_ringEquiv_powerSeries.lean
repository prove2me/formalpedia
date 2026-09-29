-- Prove2me | solution 1 for AlgebraicGeometry.smoothOfRelativeDimension_one_pullback_snd_residueField_of_forall_adicCompletion_atPrime_ringEquiv_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/88d095f3-543d-52d3-be12-919c197e30e1

import Mathlib
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_one_of_forall_nonempty_adicCompletion_stalk_ringEquiv_powerSeries
import Theorems.Thm_AdicCompletion_exists_ringEquiv_quotient_map_adicCompletion_quotient
import Theorems.Thm_IsLocalization_AtPrime_exists_ringEquiv_adicCompletion_maximalIdeal
import Theorems.Thm_AdicCompletion_exists_ringEquiv_map_of_ringEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_one_pullback_snd_residueField_of_forall_adicCompletion_atPrime_ringEquiv_powerSeries
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped TensorProduct

namespace FibreLocalForm21

theorem ker_powerSeries_map_mk {A : Type*} [CommRing A] (I : Ideal A) (hI : I.FG) :
    RingHom.ker (PowerSeries.map (Ideal.Quotient.mk I)) = I.map (PowerSeries.C (R := A)) := by
  classical
  apply le_antisymm
  · intro F hF
    rw [RingHom.mem_ker] at hF
    have hc : ∀ n, PowerSeries.coeff n F ∈ I := by
      intro n
      have := congrArg (PowerSeries.coeff n) hF
      rw [PowerSeries.coeff_map, map_zero] at this
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
    obtain ⟨s, hs⟩ := hI
    have hc' : ∀ n, ∃ c : A → A, (∑ m ∈ s, c m * m) = PowerSeries.coeff n F := by
      intro n
      have := hc n
      rw [← hs, Ideal.span, Submodule.mem_span_finset] at this
      obtain ⟨c, -, hsum⟩ := this
      exact ⟨c, by simpa [smul_eq_mul] using hsum⟩
    choose c hcsum using hc'
    have hF' : F = ∑ m ∈ s, PowerSeries.C m * PowerSeries.mk (fun n => c n m) := by
      ext n
      rw [map_sum]
      simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
      rw [← hcsum n]
      exact Finset.sum_congr rfl (fun m _ => mul_comm _ _)
    rw [hF']
    refine Ideal.sum_mem _ (fun m hm => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_))
    rw [← hs]; exact Ideal.subset_span hm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, PowerSeries.map_C, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

noncomputable def powerSeriesQuotEquiv {A : Type*} [CommRing A] (I : Ideal A) (hI : I.FG) :
    (PowerSeries A ⧸ I.map (PowerSeries.C (R := A))) ≃+* PowerSeries (A ⧸ I) :=
  (Ideal.quotEquivOfEq (ker_powerSeries_map_mk I hI).symm).trans
    (RingHom.quotientKerEquivOfSurjective (PowerSeries.map_surjective _ Ideal.Quotient.mk_surjective))

end FibreLocalForm21

open FibreLocalForm21 in
theorem solution
    (W : Type) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [IsAlgClosed (ResidueField W)]
    {S : Type} [CommRing S] [Algebra W S] [Algebra.FiniteType W S]
    (hloc : ∀ (𝔮 : Ideal S) [𝔮.IsMaximal] [𝔮.LiesOver (maximalIdeal W)],
      ∃ e : AdicCompletion (maximalIdeal (Localization.AtPrime 𝔮)) (Localization.AtPrime 𝔮) ≃+* PowerSeries W,
        ∀ a : W, e (algebraMap (Localization.AtPrime 𝔮) _
            (algebraMap S (Localization.AtPrime 𝔮) (algebraMap W S a))) = PowerSeries.C a) :
    SmoothOfRelativeDimension 1
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap W S)))
        (Spec.map (CommRingCat.ofHom (algebraMap W (ResidueField W))))) := by
  classical
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing W S
  set k := ResidueField W with hk
  set 𝔪 := maximalIdeal W with h𝔪
  set 𝔭 : Ideal S := 𝔪.map (algebraMap W S) with h𝔭

  have hiso := pullbackSpecIso_inv_snd W S k
  rw [← MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) (pullbackSpecIso W S k).inv, hiso]
  haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap W S))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 ‹Algebra.FiniteType W S›)
  have hlft : LocallyOfFiniteType ((pullbackSpecIso W S k).inv ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap W S))) (Spec.map (CommRingCat.ofHom (algebraMap W k)))) :=
    inferInstance
  rw [hiso] at hlft
  haveI := hlft
  apply AlgebraicGeometry.smoothOfRelativeDimension_one_of_forall_nonempty_adicCompletion_stalk_ringEquiv_powerSeries k
  intro y hy

  have hPmax : y.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).1 hy

  let θ : (S ⧸ 𝔭) ≃+* S ⊗[W] k := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S 𝔪).toRingEquiv
  let Qb : Ideal (S ⧸ 𝔭) := y.asIdeal.comap θ.toRingHom
  haveI hQb : Qb.IsMaximal := Ideal.comap_isMaximal_of_surjective θ.toRingHom θ.surjective
  let 𝔮 : Ideal S := Qb.comap (Ideal.Quotient.mk 𝔭)
  haveI h𝔮 : 𝔮.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have h𝔭𝔮 : 𝔭 ≤ 𝔮 := by
    intro x hx
    show Ideal.Quotient.mk 𝔭 x ∈ Qb
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]; exact Qb.zero_mem
  haveI : 𝔮.LiesOver 𝔪 := by
    refine ⟨?_⟩
    have hle : 𝔪 ≤ 𝔮.under W := by
      rw [Ideal.under_def, ← Ideal.map_le_iff_le_comap]; exact h𝔭𝔮
    exact ((IsLocalRing.maximalIdeal.isMaximal W).eq_of_le
      (fun htop => h𝔮.ne_top ((Ideal.comap_eq_top_iff).1 htop)) hle)
  have hQb𝔮 : 𝔮.map (Ideal.Quotient.mk 𝔭) = Qb := Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  have hQbP : Qb.map θ.toRingHom = y.asIdeal := Ideal.map_comap_of_surjective _ θ.surjective _

  obtain ⟨e, he⟩ := hloc 𝔮
  obtain ⟨ê₁, hê₁⟩ := IsLocalization.AtPrime.exists_ringEquiv_adicCompletion_maximalIdeal 𝔮 (Localization.AtPrime 𝔮)
  let E : AdicCompletion 𝔮 S ≃+* PowerSeries W := ê₁.trans e
  have hE : ∀ a : W, E (algebraMap S (AdicCompletion 𝔮 S) (algebraMap W S a)) = PowerSeries.C a := by
    intro a; show e (ê₁ _) = _; rw [hê₁, he]

  have hideal : (𝔭.map (algebraMap S (AdicCompletion 𝔮 S))).map (E : AdicCompletion 𝔮 S →+* PowerSeries W) =
      𝔪.map (PowerSeries.C (R := W)) := by
    rw [h𝔭, Ideal.map_map, Ideal.map_map]
    congr 1
    exact RingHom.ext (fun a => by have h__af := hE a; simp only [RingHom.comp_apply] at h__af ⊢; exact h__af)
  let e₃ : (AdicCompletion 𝔮 S ⧸ 𝔭.map (algebraMap S (AdicCompletion 𝔮 S))) ≃+* PowerSeries k :=
    (Ideal.quotientEquiv _ _ E hideal.symm).trans (powerSeriesQuotEquiv 𝔪 (IsNoetherian.noetherian 𝔪))
  obtain ⟨e₂, -⟩ := AdicCompletion.exists_ringEquiv_quotient_map_adicCompletion_quotient S 𝔮 𝔭

  let E₅ : AdicCompletion (𝔮.map (Ideal.Quotient.mk 𝔭)) (S ⧸ 𝔭) ≃+* PowerSeries k := e₂.symm.trans e₃

  obtain ⟨e₆, -⟩ := AdicCompletion.exists_ringEquiv_map_of_ringEquiv (𝔮.map (Ideal.Quotient.mk 𝔭)) θ
  have hId : (𝔮.map (Ideal.Quotient.mk 𝔭)).map (θ : (S ⧸ 𝔭) →+* S ⊗[W] k) = y.asIdeal := by
    rw [hQb𝔮]; exact hQbP
  have h7 : Nonempty (AdicCompletion y.asIdeal (S ⊗[W] k) ≃+* PowerSeries k) := by
    rw [← hId]; exact ⟨e₆.symm.trans E₅⟩
  obtain ⟨E₇⟩ := h7

  letI : Algebra (S ⊗[W] k) ((Spec (CommRingCat.of (S ⊗[W] k))).presheaf.stalk y) :=
    StructureSheaf.stalkAlgebra (S ⊗[W] k) y
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of (S ⊗[W] k))).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (S ⊗[W] k) y
  haveI := hPmax
  obtain ⟨e₈, -⟩ := IsLocalization.AtPrime.exists_ringEquiv_adicCompletion_maximalIdeal y.asIdeal
    ((Spec (CommRingCat.of (S ⊗[W] k))).presheaf.stalk y)
  exact ⟨e₈.symm.trans E₇⟩

end S_AlgebraicGeometry_smoothOfRelativeDimension_one_pullback_snd_residueField_of_forall_adicCompletion_atPrime_ringEquiv_powerSeries
end P2MW
export P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_one_pullback_snd_residueField_of_forall_adicCompletion_atPrime_ringEquiv_powerSeries (solution)
